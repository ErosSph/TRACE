#!/usr/bin/env python3
"""Fetch-ROM link (item 2): the word entering IF/ID (the input wire 137 of the instruction register) is the ROM word at the
fetch pc.  Chain traced from the AST: 137 <- 15 <- 2 <- 329 (imem.o_instr = ESel 32 rom (ESel 12 ((pc[31:2]) << 5) 0)), address 328 <- 3 <- 17 <- 26 <- 119.
The imem lookup expression is exactly ExtendedSVPackedROM.lookup 101 12; with the ROM root 330 = pack words (invariant: 330 is only
written by the seed, and environment events change only the root inputs 0/1) the fetched word is `nth i words 0` for pc = 4*i.
Reused low-level facts: none beyond Bootstrap/WriteValidityBoot definitions (F.seed, F.boot_events, Environment).
Untrusted generator. proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0."""
import json
import sys
from pathlib import Path
import cpu_tmpl_ast as T
import cpu_tmpl_roles as roles

REF = Path('results/r-jump-itree-20261102-a2')


def text():
    ast, pr, tr = roles.load_all('bzeeno')
    rom = pr['ram'] and 330
    chain_in = [137, 15, 2]       # copies down to imem.o_instr
    chain_pc = [328, 3, 17, 26]   # address copies down to the pc register 119
    L = []
    for s in chain_in + chain_pc + [329]:
        cc = ast.comb[s]
        W = cc['width']
        L += [f'Definition orig_w{s}:Expr:={T.coq(cc["rhs"])}.',
              f'Theorem eq_w{s} seed fixed:CombLFP P seed fixed->norm {W}(read_signal fixed {s}%nat)=norm {W}(eval_expr fixed orig_w{s}).',
              f'Proof. intro HL. refine(checked_assignment_binding P _ {cc["k"]}%nat {cc["name"]} false orig_w{s} {W}%nat {s}%nat seed fixed eq_refl _ _ _ _ HL).',
              ' all: first[vm_compute;reflexivity|(vm_compute;lia)]. Qed.']
    L += ['Theorem pc_chain seed d : CombLFP P seed d -> norm 32(read_signal d 328%nat)=norm 32(read_signal d 119%nat).',
          'Proof. intro HL. rewrite(eq_w328 seed d HL). unfold orig_w328. cbn[eval_expr]. rewrite norm_idempotent.',
          ' rewrite(eq_w3 seed d HL). unfold orig_w3. cbn[eval_expr]. rewrite norm_idempotent.',
          ' rewrite(eq_w17 seed d HL). unfold orig_w17. cbn[eval_expr]. rewrite norm_idempotent.',
          ' rewrite(eq_w26 seed d HL). unfold orig_w26. cbn[eval_expr]. rewrite norm_idempotent. reflexivity. Qed.',
          'Theorem instr_chain seed d : CombLFP P seed d -> norm 32(read_signal d 137%nat)=norm 32(read_signal d 329%nat).',
          'Proof. intro HL. rewrite(eq_w137 seed d HL). unfold orig_w137. cbn[eval_expr]. rewrite norm_idempotent.',
          ' rewrite(eq_w15 seed d HL). unfold orig_w15. cbn[eval_expr]. rewrite norm_idempotent.',
          ' rewrite(eq_w2 seed d HL). unfold orig_w2. cbn[eval_expr]. rewrite norm_idempotent. reflexivity. Qed.',
          # the lookup: eval of the imem expression at d equals ExtendedSVPackedROM.lookup on the (normalised) address
          'Theorem imem_lookup seed d (image : Z) : CombLFP P seed d -> read_signal d 330%nat = image ->',
          ' norm 32(read_signal d 329%nat)=ExtendedSVPackedROM.lookup 101 12 image (norm 32(read_signal d 328%nat)).',
          'Proof. intros HL HR. rewrite(eq_w329 seed d HL). unfold orig_w329, ExtendedSVPackedROM.lookup. cbn[eval_expr]. rewrite HR.',
          ' rewrite ?norm_idempotent. reflexivity. Qed.',
          'Theorem fetch_word seed d (words : list Z) (i : nat) : CombLFP P seed d -> read_signal d 330%nat = ExtendedSVPackedROM.pack words ->',
          ' Forall (Word 32) words -> (i < 101)%nat -> norm 32(read_signal d 119%nat) = 4 * Z.of_nat i ->',
          ' norm 32(read_signal d 137%nat) = norm 32(nth i words 0).',
          'Proof. intros HL HR HW HI HP. rewrite(instr_chain seed d HL). rewrite(imem_lookup seed d _ HL HR). rewrite(pc_chain seed d HL). rewrite HP.',
          ' apply ExtendedSVPackedROM.lookup_packed; [exact HW|exact HI|change (Z.of_nat i < 33554432); lia|change (32 * Z.of_nat i < 4096); lia]. Qed.',
          '',
          '(* ROM invariant: the ROM root is only written by the seed; environment events change only the input roots 0 and 1 *)',
          'Lemma rom_unwritten : roots_unwrittenb 330%nat (processes P) = true. Proof. vm_compute; reflexivity. Qed.',
          'Lemma ev_not_rom ev : Environment ev -> changed_signal ev <> 330%nat.',
          'Proof. intros [_ HE]. unfold ExternalEvent in HE. apply existsb_exists in HE as [r [Hin Hr]]. apply Nat.eqb_eq in Hr. rewrite Hr.',
          ' unfold external_roots in Hin. cbn in Hin. repeat destruct Hin as [<-|Hin]; try contradiction; discriminate. Qed.',
          'Lemma rom_phase ev pre : Environment ev -> read_signal (PhaseSemantics P ev pre) 330%nat = read_signal pre 330%nat.',
          'Proof. intro HE. rewrite(phase_input P 330%nat ev pre rom_unwritten). apply read_signal_write_other. intro H. apply (ev_not_rom ev HE). congruence. Qed.',
          'Lemma rom_run events : Forall Environment events -> forall pre, read_signal (phase_run P events pre) 330%nat = read_signal pre 330%nat.',
          'Proof. intro HE. induction HE as [|ev rest Hev HR IH]; intro pre; [rewrite phase_run_nil; reflexivity|].',
          ' rewrite phase_run_cons, IH. apply rom_phase. exact Hev. Qed.',
          'Lemma seed_rom image : read_signal (F.seed image) 330%nat = image.',
          'Proof. unfold F.seed, F.writes, ExtendedSVBootstrap.seed_writes. cbn[fold_left fst snd]. rewrite read_signal_write_other by discriminate. apply read_signal_write_same. Qed.',
          'Theorem rom_inv (words : list Z) events : Forall Environment events -> read_signal (phase_run P events (F.boot (ExtendedSVPackedROM.pack words))) 330%nat = ExtendedSVPackedROM.pack words.',
          'Proof. intro HE. rewrite (rom_run events HE). unfold F.boot. rewrite (rom_run F.boot_events boot_environment). apply seed_rom. Qed.']
    return L


HDR = r"""From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVCheckedAssignmentBinding Lang.ExtendedSVWordInvariant Lang.ExtendedSVStallFlush Lang.ExtendedSVBankAlignment
 GeneratedRuntimeInput.ConfiguredAST.
Import ListNotations ExtendedSV ExtendedSVCheckedAssignmentBinding ExtendedSVWordInvariant ExtendedSVStallFlush ExtendedSVBankAlignment.
Import BzeenoLoadUseJalASTConfigured3122be4a95.
Require Import Lang.ExtendedSVScalarHistory Lang.ExtendedSVPackedROM Lang.ExtendedSVEmptyPipeline Lang.ExtendedSVConstantRoot Lang.ExtendedSVBootstrap
 GeneratedSeedBoot.FrozenEnvironment GeneratedWriteValidityBoot.WriteValidityBoot.
Import ExtendedSVScalarHistory ExtendedSVEmptyPipeline ExtendedSVConstantRoot.
Local Open Scope Z_scope.
Local Opaque PhaseSemantics BzeenoLoadUseJalASTConfigured3122be4a95.bzeeno_load_use_jal_program.
Module F := GeneratedSeedBoot.FrozenEnvironment.
Lemma phase_run_cons : forall p ev rest pre, phase_run p (ev :: rest) pre = phase_run p rest (PhaseSemantics p ev pre).
Proof. reflexivity. Qed.
Lemma phase_run_nil : forall p pre, phase_run p [] pre = pre.
Proof. reflexivity. Qed.
Local Opaque phase_run.
"""


def build(module='BzTmplFetch'):
    names = ['fetch_word', 'rom_inv']
    body = ('(** bzeeno: fetch-ROM link (tools/cpu_tmpl_bzfetch.py). proof_author: ' + T.PROOF_AUTHOR + '; external_llm_api_calls=0. *)\n' + HDR +
            f'Module {module}.\nNotation P := bzeeno_load_use_jal_program (only parsing).\n' + '\n'.join(text()) + f'\nEnd {module}.\n' +
            ''.join(f'Print Assumptions {module}.{n}.\n' for n in names))
    return body, [f'{module}.{n}' for n in names]


if __name__ == '__main__':
    body, exports = build()
    if len(sys.argv) > 2 and sys.argv[2] == '--accept':
        import cpu_tmpl_accept as acc
        prov = json.loads((REF / 'providers.json').read_text())
        r = acc.accept(sys.argv[1], 'TmplBzFetch', 'BzTmplFetch', body, exports, [], providers=prov, extra=dict(generator='tools/cpu_tmpl_bzfetch.py', design='bzeeno'))
        print(json.dumps({k: r[k] for k in r if k in ('accepted', 'coqc_seconds', 'coqchk_seconds', 'assumptions')}))
    else:
        Path(sys.argv[1]).write_text(body)
