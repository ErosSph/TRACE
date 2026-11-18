#!/usr/bin/env python3
"""Generate a pipeline obligation skeleton (Coq) from a design manifest.

The skeleton is a Coq module that, for one pipelined design:
  * defines the design as a generic ``StagedDesign`` record;
  * states every per-design obligation as a named ``Prop`` (``goal_*``);
  * proves one assembled theorem: all goals -> actual reset refines the ISA
    ITree forever (``assembled``), through the generic pipeline route.
It contains no ``Admitted`` and no axioms: the goals are premises, not
assumptions. A design is finished when every goal is proved.

Modes (which generic obligation list the goals come from):
  plan    CPUPipelineObligations.CycleObligations   (single retire, 6 goals)
  plan_m  CPUPipelineObligationsM.CycleObligationsM (0..2 retires, 7 goals)
  ctx     CPUPipelineStagedContext.StagedObligationCtx (1 goal; shape chosen
          per cycle, for designs without a computable cycle plan)
  m       CPUPipelineCycle2.StagedObligationM       (1 goal, multi-retire)
  rh      CPUPipelineRetireHold.StagedObligationRH  (1 goal; m plus the retire-and-hold case)
Every mode adds three goals: rank (silent cycles decrease), boot (relation
at the boot state) and startup (reset ITree = boot ITree).

With a ``fill`` section the generator also writes ``<module>Fill``: it proves
every goal from the given (accepted) terms, derives the final theorem from
``assembled``, and type-checks the reference proof term against the same
statement (``same_statement_as_reference``).

Usage: cpu_pipeline_skeleton.py MANIFEST.json [--out-dir src/Ex/External]
"""
import argparse
import json
import pathlib
import sys

PROOF_AUTHOR = "LLM-generated: Claude Code (claude-opus-5-5)"

GENERIC_REQUIRES = [
    "Ex.External.CPUGeneratedJointTemplate", "Ex.External.CPUGeneratedJointITree", "Ex.External.CPUPipelineQueue",
    "Ex.External.CPUPipelineStages", "Ex.External.CPUPipelineStagesContext",
    "Ex.External.CPUPipelineMultiRetire", "Ex.External.CPUPipelineCycle",
    "Ex.External.CPUPipelineStaged", "Ex.External.CPUPipelineStagedContext",
    "Ex.External.CPUPipelineCycle2", "Ex.External.CPUPipelineObligations",
    "Ex.External.CPUPipelineObligationsM", "Ex.External.CV32E40PTwoCommitITreeInterface",
    "Ex.RvCore.FormalSpec",
]
GENERIC_IMPORTS = [
    "ListNotations", "CPUGeneratedJointTemplate", "CPUGeneratedJointITree", "CPUPipelineQueue", "CPUPipelineStages",
    "CPUPipelineStagesContext", "CPUPipelineMultiRetire", "CPUPipelineCycle", "CPUPipelineStaged",
    "CPUPipelineStagedContext", "CPUPipelineCycle2", "CPUPipelineObligations",
    "CPUPipelineObligationsM", "CV32E40PTwoCommitITreeInterface",
]
FIELDS = ["step", "commits", "effect", "pc", "effect_sound", "stages", "arch", "front", "stage"]
PHYS = "forall s retired frontier,staged_physical @D@ s retired frontier->"

# (goal name, statement after the shared [forall s retired frontier, physical ->] prefix)
PLAN_GOALS = [
    ("shape", "sd_stages @D@(sd_step @D@ s)=shape_post(@PS@ s)(sd_stages @D@ s)"),
    ("transport", "shape_transport_ctx(sd_effect @D@)(@PS@ s)(sd_stage @D@ s)(sd_stage @D@(sd_step @D@ s))retired(sd_stages @D@ s)"),
    ("admission", "shape_admission(sd_effect @D@)(@PS@ s)(sd_stage @D@(sd_step @D@ s))(sd_stages @D@ s)frontier(@PN@ s retired frontier)"),
    ("observer", "sd_commits @D@ s=observe(to_pipeline @D@)(shape_retiring(@PS@ s)(sd_stages @D@ s))"),
    ("front", "sd_front @D@(sd_step @D@ s)(@PN@ s retired frontier)"),
    ("arch", "forall advanced,EffectChain(sd_effect @D@)retired(shape_retiring(@PS@ s)(sd_stages @D@ s))advanced->sd_arch @D@(sd_step @D@ s)advanced"),
]
PLAN_M_GOALS = [
    ("shape", "sd_stages @D@(sd_step @D@ s)=shapem_post(@PS@ s)(sd_stages @D@ s)"),
    ("bounds", "shapem_bounds(@PS@ s)(sd_stages @D@ s)"),
    ("transport", "shapem_transport(sd_effect @D@)(@PS@ s)(sd_stage @D@ s)(sd_stage @D@(sd_step @D@ s))retired(sd_stages @D@ s)"),
    ("admission", "shapem_admission(sd_effect @D@)(@PS@ s)(sd_stage @D@(sd_step @D@ s))(sd_stages @D@ s)frontier(@PN@ s retired frontier)"),
    ("observer", "sd_commits @D@ s=observe2(to_pipeline @D@)(shapem_retiring(@PS@ s)(sd_stages @D@ s))"),
    ("front", "sd_front @D@(sd_step @D@ s)(@PN@ s retired frontier)"),
    ("arch", "forall advanced,EffectChain(sd_effect @D@)retired(shapem_retiring(@PS@ s)(sd_stages @D@ s))advanced->sd_arch @D@(sd_step @D@ s)advanced"),
]
MODES = {
    "plan": ("CycleObligations", "Build_CycleObligations", "obligations_infinite_refinement", PLAN_GOALS),
    "plan_m": ("CycleObligationsM", "Build_CycleObligationsM", "obligations_m_infinite_refinement", PLAN_M_GOALS),
    "ctx": ("StagedObligationCtx", None, "staged_ctx_infinite_refinement", None),
    "m": ("StagedObligationM", None, "staged_m_infinite_refinement", None),
    "rh": ("StagedObligationRH", None, "staged_rh_infinite_refinement", None),
}
# Modes whose generic list lives in an additional generic module: (requires, imports).
MODE_EXTRA = {
    "rh": (["Ex.External.CPUPipelineRetireHold"], ["CPUPipelineRetireHold"]),
}


def wrap(items, indent=" "):
    """Join names into lines of at most ~100 characters."""
    lines, cur = [], ""
    for it in items:
        if cur and len(cur) + len(it) + 1 > 100:
            lines.append(cur)
            cur = indent + it
        else:
            cur = (cur + " " + it) if cur else it
    lines.append(cur)
    return "\n".join(lines)


def header(doc, requires, imports, prelude, author=PROOF_AUTHOR):
    out = [f"(** {doc}\n\n    proof_author: {author}; external_llm_api_calls=0.\n    Generated by tools/cpu_pipeline_skeleton.py; do not edit by hand. *)"]
    out.append("From Coq Require Import ZArith List Lia.\nFrom ITree Require Import ITree ITreeFacts.")
    out.append("Require Import " + wrap(requires) + ".")
    out.append("Import " + wrap(imports) + ".")
    out.append("Local Open Scope itree_scope.")
    out.extend(prelude)
    return "\n".join(out)


def goal_names(mode):
    names = [g for g, _ in MODES[mode][3]] if MODES[mode][3] else ["obligation"]
    return names + ["rank", "boot", "startup"]


def statement(m):
    return (f"ordered_scheduler({m['fields']['step']})({m['fields']['commits']})({m['reset']}) ≈\n"
            f" FormalSpec.riscv_itree_with_state({m['initial']})")


def skeleton(m):
    mode = m["mode"]
    if mode not in MODES:
        sys.exit(f"unknown mode {mode!r}; expected one of {sorted(MODES)}")
    record, build, refinement, goals = MODES[mode]
    if goals and ("plan_shape" not in m or "plan_next" not in m):
        sys.exit(f"mode {mode} needs plan_shape and plan_next")
    P, A, f = m["params"], m["args"], m["fields"]
    D = f"(design {A})"
    doc = (f"Pipeline obligation skeleton for {m['design']} (mode {mode}, generic list [{record}]).\n\n"
           "    Each [goal_*] is one per-design obligation; [assembled] proves that all\n"
           "    of them together give the infinite RTL->ISA ITree refinement from actual\n"
           "    reset. The goals are premises, not axioms.")
    xreq, ximp = MODE_EXTRA.get(mode, ([], []))
    body = [header(doc, GENERIC_REQUIRES + xreq + m.get("requires", []), GENERIC_IMPORTS + ximp + m.get("imports", []),
                   m.get("prelude", []), m.get("proof_author", PROOF_AUTHOR)),
            f"Module {m['module']}."]
    body.extend(m.get("module_prelude", []))
    body.append("Section Skeleton.")
    if m.get("context"):
        body.append(m["context"])
    body.append("")
    body.append(f"Definition design{P}:StagedDesign({m['runtime']})({m['token']}):={{|")
    body.append(" " + ";\n ".join(f"sd_{k}:={f[k]}" for k in FIELDS) + "|}.")
    if goals:
        body.append(f"Definition plan_shape{P}:=({m['plan_shape']}).")
        body.append(f"Definition plan_next{P}:=({m['plan_next']}).")
        for name, stmt in goals:
            text = stmt.replace("@D@", D).replace("@PS@", f"(plan_shape {A})").replace("@PN@", f"(plan_next {A})")
            body.append(f"Definition goal_{name}{P}:Prop:=\n {PHYS.replace('@D@', D)}\n  {text}.")
    else:
        body.append(f"Definition goal_obligation{P}:Prop:={record}{D}.")
    step, commits = f["step"], f["commits"]
    body.append(f"Definition goal_rank{P}:Prop:=\n OrderedWaitDecreases({step})({commits})(PipelineJoint(to_pipeline{D}))({m['rank']}).")
    body.append(f"Definition goal_boot{P}:Prop:=\n PipelineJoint(to_pipeline{D})({m['boot']})({m['initial']}).")
    body.append(f"Definition goal_startup{P}:Prop:=\n ordered_scheduler({step})({commits})({m['reset']}) ≈\n"
                f" ordered_scheduler({step})({commits})({m['boot']}).")
    names = goal_names(mode)
    hyps = "->".join(f"goal_{n} {A}" for n in names)
    hnames = " ".join(f"G_{n}" for n in names)
    body.append("")
    body.append(f"(** All goals together give the refinement from actual reset. *)")
    body.append(f"Theorem assembled{P}:\n {hyps}->\n {statement(m)}.")
    body.append(f"Proof. intros {hnames}.")
    body.append(f" transitivity(ordered_scheduler({step})({commits})({m['boot']}));[exact G_startup|].")
    if goals:
        built = f"({build} _ _ _ " + " ".join(f"G_{g}" for g, _ in goals) + ")"
        body.append(f" exact({refinement}{D}(plan_shape {A})(plan_next {A})({m['rank']})\n  {built} G_rank _ _ G_boot).")
    else:
        body.append(f" exact({refinement}{D}({m['rank']})G_obligation G_rank _ _ G_boot).")
    body.append("Qed.")
    body.append("End Skeleton.")
    body.append(f"End {m['module']}.")
    body.append(f"Print Assumptions {m['module']}.assembled.")
    return "\n".join(body) + "\n"


def fill(m):
    fl, mod, P, A = m["fill"], m["module"], m["params"], m["args"]
    names = goal_names(m["mode"])
    missing = [n for n in names if n not in fl["goals"]]
    if missing:
        sys.exit(f"fill section lacks goals: {missing}")
    fmod = mod + "Fill"
    doc = (f"{m['design']}: every goal of [{mod}] proved from accepted lemmas.\n\n"
           "    [filled] is the final theorem through the skeleton; [same_statement_as_reference]\n"
           "    type-checks the reference proof against the same statement.")
    xreq, ximp = MODE_EXTRA.get(m["mode"], ([], []))
    reqs = GENERIC_REQUIRES + xreq + m.get("requires", []) + fl.get("requires", []) + [f"Ex.External.{mod}"]
    imps = GENERIC_IMPORTS + ximp + m.get("imports", []) + fl.get("imports", [])
    body = [header(doc, reqs, imps, m.get("prelude", []), m.get("proof_author", PROOF_AUTHOR)), f"Module {fmod}."]
    body.extend(m.get("module_prelude", []))
    body.append(f"Module S:={mod}.{mod}.")
    body.append("Section Fill.")
    if m.get("context"):
        body.append(m["context"])
    for n in names:
        body.append(f"Theorem goal_{n}_holds{P}:S.goal_{n} {A}.\nProof. unfold S.goal_{n}. exact({fl['goals'][n]}). Qed.")
    proofs = " ".join(f"(goal_{n}_holds {A})" for n in names)
    body.append(f"Theorem filled{P}:\n {statement(m)}.\nProof. exact(S.assembled {A} {proofs}). Qed.")
    body.append(f"Theorem same_statement_as_reference{P}:\n {statement(m)}.\nProof. exact({fl['reference']}). Qed.")
    body.append("End Fill.")
    body.append(f"End {fmod}.")
    body.append(f"Print Assumptions {fmod}.filled.")
    body.append(f"Print Assumptions {fmod}.same_statement_as_reference.")
    return fmod, "\n".join(body) + "\n"


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("manifest")
    ap.add_argument("--out-dir", default="src/Ex/External")
    a = ap.parse_args()
    m = json.loads(pathlib.Path(a.manifest).read_text())
    out = pathlib.Path(a.out_dir)
    path = out / f"{m['module']}.v"
    path.write_text(skeleton(m))
    print(path)
    if "fill" in m:
        fmod, text = fill(m)
        (out / f"{fmod}.v").write_text(text)
        print(out / f"{fmod}.v")


if __name__ == "__main__":
    main()
