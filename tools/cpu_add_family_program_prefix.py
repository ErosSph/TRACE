"""Static original-ISA ADD/ADDI ROM certificates and bounded real cycles.

Cycle composition is enabled only for the accepted new family-cycle provider;
the program certificate has no CPU correctness or future-state premise.
"""
import argparse
import json
from pathlib import Path
import re
import time

import cpu_add_family_memory_joint as memory
from cpu_certificate_acceptance import run_stage,parse_assumptions,ALLOWED_AXIOMS
from check_reference_value_rules import audit_all_exports


def validate_domain(plan):
    capacity,offset=plan['capacity'],plan['offset_width']
    if not(0<capacity<=2**25 and 32*(capacity-1)<2**offset):
        raise ValueError('original ROM domain/alias certificate required')
    return capacity,offset


def render_static(c,profile,plan):
    capacity,offset=validate_domain(plan)
    fj='GeneratedFetchReference.FetchReference'
    m='GeneratedAddFamilyMemoryJoint.AddFamilyMemoryJoint'
    source=f'''From Coq Require Import List ZArith Bool Lia.
Require Import {c['ast_module']} Lang.ExtendedSV Lang.ExtendedSVWordInvariant Lang.ExtendedSVScalarHistory
 Lang.ExtendedSVPackedROM Lang.ExtendedSVCaptureBirth Ex.External.CPUGeneratedJointTemplate
 Ex.External.CPUOriginalISAReference Ex.RvCore.FormalSpec coqutil.Word.Interface coqutil.Word.Properties
 coqutil.Word.Bitwidth coqutil.Map.Interface coqutil.Byte
 GeneratedAddFamilyMemoryJoint.AddFamilyMemoryJoint GeneratedFetchReference.FetchReference.
Import ListNotations ExtendedSV ExtendedSVWordInvariant ExtendedSVScalarHistory ExtendedSVCaptureBirth CPUGeneratedJointTemplate.
Local Open Scope Z_scope.
Definition FamilyWord code:Prop:=
 (exists rd rs1 rs2,Decode.decode Decode.RV32I code=Decode.IInstruction(Decode.Add rd rs1 rs2)) \/
 (exists rd rs imm,Decode.decode Decode.RV32I code=Decode.IInstruction(Decode.Addi rd rs imm)).
Definition family_wordb code:bool:=match Decode.decode Decode.RV32I code with
 |Decode.IInstruction(Decode.Add _ _ _)=>true
 |Decode.IInstruction(Decode.Addi _ _ _)=>true
 |_=>false end.
Definition FamilyProgram words:Prop:=Forall(Word 32)words /\\Forall FamilyWord words /\\(length words<={capacity})%nat.
Definition family_programb words:bool:=
 forallb(fun code=>Z.eqb code(norm 32 code)&&family_wordb code)words && Nat.leb(length words){capacity}.
Theorem family_wordb_sound code:family_wordb code=true ->FamilyWord code.
Proof. unfold family_wordb;destruct(Decode.decode Decode.RV32I code)eqn:HD;try discriminate;
 destruct iInstruction;try discriminate;intro H;unfold FamilyWord;
 first[left;repeat eexists;exact HD|right;repeat eexists;exact HD]. Qed.
Theorem family_programb_sound words:family_programb words=true ->FamilyProgram words.
Proof. unfold family_programb,FamilyProgram;intro HB;apply Bool.andb_true_iff in HB as[HW HL].
 apply Nat.leb_le in HL.
 pose proof(proj1(@forallb_forall Z(fun code=>Z.eqb code(norm 32 code)&&family_wordb code)words)HW)as HWords.
 assert(HBoth:Forall(fun code=>Word 32 code /\\FamilyWord code)words).
 {{ apply(proj2(@Forall_forall Z _ words));intros code HI;specialize(HWords code HI);apply Bool.andb_true_iff in HWords as[HN HD].
    split;[apply Z.eqb_eq in HN;exact HN|exact(family_wordb_sound code HD)]. }}
 split.
 - apply(proj2(@Forall_forall Z(Word 32)words));intros code HI.
   exact(proj1((proj1(@Forall_forall Z _ words)HBoth)code HI)).
 - split;[|exact HL];apply(proj2(@Forall_forall Z FamilyWord words));intros code HI.
   exact(proj2((proj1(@Forall_forall Z _ words)HBoth)code HI)). Qed.
Theorem family_word_token token:FamilyWord(token_word token)<->{m}.FamilyToken token.
Proof. reflexivity. Qed.
Theorem actual_image_bounds words i:FamilyProgram words ->(i<length words)%nat ->
 Z.of_nat(length words)<=2^30 /\\(i<{capacity})%nat /\\Z.of_nat i<2^25 /\\32*Z.of_nat i<2^Z.of_nat {offset}%nat.
Proof. intros[HW[HD HL]]HI;assert(HCap:(i<{capacity})%nat)by lia.
 split;[change(Z.of_nat(length words)<=1073741824);lia|];split;[exact HCap|];split.
 - change(Z.of_nat i<33554432);lia.
 - change(32*Z.of_nat i<{2**offset});lia.
Qed.
Theorem actual_image_family words i:FamilyProgram words ->(i<length words)%nat ->
 FamilyWord({fj}.R.lookup(ExtendedSVPackedROM.pack words)(4*Z.of_nat i)).
Proof. intros HP HI;pose proof HP as[HW[HD HL]].
 destruct(actual_image_bounds words i HP HI)as[HLen[HC[HIndex HOffset]]].
 assert(HWord:Word 32(nth i words 0)).
 {{ apply(proj1(Forall_forall _ _)HW);apply nth_In;exact HI. }}
 assert(HDecode:FamilyWord(nth i words 0)).
 {{ apply(proj1(Forall_forall _ _)HD);apply nth_In;exact HI. }}
 assert(HLookup:{fj}.R.lookup(ExtendedSVPackedROM.pack words)(4*Z.of_nat i)=nth i words 0).
 {{ exact(eq_trans({fj}.lookup_is_original_expression _ _)
    (eq_trans(ExtendedSVPackedROM.lookup_packed {capacity}%nat {offset}%nat words i HW HC HIndex HOffset)(eq_sym HWord))). }}
 now rewrite HLookup.
Qed.
Example rejects_store:family_programb[35]=false. Proof. vm_compute;reflexivity. Qed.
Example rejects_xori:family_programb[16531]=false. Proof. vm_compute;reflexivity. Qed.
Example accepts_mixed_family:family_programb[3211443;1114259]=true. Proof. vm_compute;reflexivity. Qed.
Example rejects_over_capacity:family_programb(repeat 19 {capacity+1})=false. Proof. vm_compute;reflexivity. Qed.
'''
    exports=['family_wordb_sound','family_programb_sound','family_word_token','actual_image_bounds','actual_image_family',
             'rejects_store','rejects_xori','accepts_mixed_family','rejects_over_capacity']
    return source,exports


def render(c,profile,plan):
    source,exports=render_static(c,profile,plan)
    p=profile['ast']['program'];h='GeneratedCapturedHistoryBoot.CapturedHistoryBoot';f=h+'.F'
    clock='GeneratedClockCycleJoint.CycleJoint';cycle='GeneratedAddFamilyMemoryCycle.AddFamilyMemoryCycle'
    m='GeneratedAddFamilyMemoryJoint.AddFamilyMemoryJoint';fi='GeneratedFrontierInitial.FrontierInitial'
    ref='GeneratedFetchReference.FetchReference';nw='GeneratedNormalWrite.NormalWrite';cp='GeneratedCommitPC.CommitPC'
    image='(ExtendedSVPackedROM.pack words)';evs='(cycle_events cycles)'
    pre=f'(phase_run {p} {evs}({f}.boot {image}))';packed=f'({h}.boot_history {image} {evs})'
    effect=f'(CPUOriginalISAReference.instruction_effect {ref}.recorded_pc token_word)'
    enable=plan['enable_root']
    test=f'Z.eqb(norm 1(read_signal(phase_driven_state {p} {f}.rise(phase_run {p}(cycle_events n)({f}.boot {image}))){enable}%nat))0%Z'
    next_i=f'(if {test} then i else S i)'
    source+=f'''Require Import GeneratedAddFamilyMemoryCycle.AddFamilyMemoryCycle GeneratedClockCycleJoint.CycleJoint
 GeneratedNormalWrite.NormalWrite GeneratedCommitPC.CommitPC GeneratedFrontierInitial.FrontierInitial.
Fixpoint cycle_events(count:nat):list Event:=match count with
 |O=>[]|S n=>(cycle_events n++[{f}.rise])++[{f}.fall]end.
Definition cycle_commits image events:=
 {nw}.actual_RF_commits(phase_run {p}(events++[{f}.rise])({f}.boot image))
 ({h}.boot_history image(events++[{f}.rise])).
Definition cycle_pcs image events:=
 {cp}.actual_visible_commits(phase_run {p}(events++[{f}.rise])({f}.boot image)).
Fixpoint retired_prefix image(count:nat):list Token:=match count with
 |O=>[]|S n=>retired_prefix image n++cycle_commits image(cycle_events n)end.
Fixpoint visible_prefix image(count:nat):list Z:=match count with
 |O=>[]|S n=>visible_prefix image n++cycle_pcs image(cycle_events n)end.
Lemma no_events program pre:phase_run program[]pre=pre. Proof. reflexivity. Qed.
Local Opaque {p} PhaseSemantics phase_run {f}.boot {h}.boot_history.
Theorem actual_cycle_environment count:Forall {h}.W.Environment(cycle_events count).
Proof. induction count as[|n IH];cbn[cycle_events];[constructor|].
 apply Forall_app;split.
 - apply Forall_app;split;[exact IH|constructor;[apply {clock}.scheduled_event_allowed;now left|constructor]].
 - constructor;[apply {clock}.scheduled_event_allowed;right;now left|constructor]. Qed.
Section OriginalISA.
Context {{word:Interface.word 32}}{{BW:Bitwidth 32}}{{Registers:map.map Z word}}{{Mem:map.map word byte}}
 {{word_ok:word.ok word}}{{registers_ok:map.ok Registers}}{{mem_ok:map.ok Mem}}.
Theorem actual_family_program_prefix words cycles:FamilyProgram words ->(cycles<=length words)%nat ->
 exists i committed,(i<=cycles)%nat /\\{clock}.ClockBoundary {pre} /\\
 EffectChain {effect}({fi}.original_initial words)(retired_prefix {image} cycles)committed /\\
 EffectChain CPUOriginalISAReference.original_step({fi}.original_initial words)(retired_prefix {image} cycles)committed /\\
 visible_prefix {image} cycles=map {ref}.recorded_pc(retired_prefix {image} cycles) /\\
 {m}.FamilyMemoryJoint words i({fi}.original_initial words)(retired_prefix {image} cycles)committed {pre} {packed}.
Proof. intro HProgram;induction cycles as[|n IH];intro HCount.
 - cbn[cycle_events retired_prefix visible_prefix];rewrite no_events.
   destruct({m}.actual_boot_boundary_and_family_joint words)as[HB HJ].
   exists 0%nat,({fi}.original_initial words);split;[lia|];split;[exact HB|].
   split;[constructor|];split;[constructor|];split;[reflexivity|exact HJ].
 - destruct(IH ltac:(lia))as[i[committed[HI[HB[HChain[HRun[HVisible HJoint]]]]]]].
   assert(HIn:(i<length words)%nat)by lia.
   destruct(actual_image_bounds words i HProgram HIn)as[HLen[HCap[HIndex HOffset]]].
   pose proof(actual_image_family words i HProgram HIn)as HD.
   pose proof(proj1 HProgram)as HW.
   destruct({cycle}.actual_family_memory_cycle words i({fi}.original_initial words)
     (retired_prefix {image} n)committed(cycle_events n)
     HW HLen HCap HIndex HOffset(actual_cycle_environment n)HB HJoint HD)
     as[next[HC[HOriginal[HObserve[HQueue[HNext HBoundary]]]]]].
   exists {next_i},next;split.
   + destruct({test});lia.
   + split;[exact HBoundary|];split.
     * exact(chain_append {effect} _ _ _ _ _ HChain HC).
     * split.
       {{ exact(chain_append CPUOriginalISAReference.original_step _ _ _ _ _ HRun HOriginal). }}
       split;[|exact HNext].
       change(visible_prefix {image} n++cycle_pcs {image}(cycle_events n)=
         map {ref}.recorded_pc(retired_prefix {image} n++cycle_commits {image}(cycle_events n))).
       rewrite map_app;exact(f_equal2(@app Z)HVisible HObserve).
Qed.
End OriginalISA.
Goal True. idtac "FAMILY_PROGRAM_AUDIT". exact I. Qed.
'''
    exports+=['actual_cycle_environment','actual_family_program_prefix']
    source+=''.join(f'Print Assumptions {name}.\n'for name in exports)
    return source,exports


def check(c,cycle_provider,output):
    provider=Path(cycle_provider);receipt=json.loads((provider/'report.json').read_text());file=provider/'AddFamilyMemoryCycle.v'
    if not(receipt.get('accepted')and receipt.get('assumptions_audit_passed')and receipt['coqc_exit']==receipt['coqchk_exit']==0 and receipt['old_inv_read']is False
        and memory.digest(file.read_bytes())==receipt['source_sha256']
        and memory.digest(file.with_suffix('.vo').read_bytes())==receipt['object_sha256']):
        raise ValueError('accepted unchanged new family cycle required before native prefix composition')
    raw,profile,_=memory.family.derived.controls.history.admission.observation.origin.raw_binding(c['ast'],c['ast_module'])
    if receipt['ast_sha256']!=raw['source_sha256']:raise ValueError('original program/AST configuration mismatch')
    paths=json.loads((provider/'providers.json').read_text())
    memory_path=next(row['directory']for row in paths if row['namespace']=='GeneratedAddFamilyMemoryJoint')
    plan=json.loads((Path(memory_path)/'plan.json').read_text());validate_domain(plan)
    paths.append(dict(namespace='GeneratedAddFamilyMemoryCycle',directory=str(provider.resolve())))
    source,exports=render(c,profile,plan)
    out=Path(output);out.mkdir(parents=True,exist_ok=False);file=out/'AddFamilyProgramPrefix.v';file.write_text(source)
    for name,data in [('providers',paths),('exports',exports),('plan',plan),('inputs',c)]:
        (out/(name+'.json')).write_text(json.dumps(data,indent=2)+'\n')
    flags=list(memory.family.derived.rtl.framework.FLAGS)
    for row in paths:flags+=['-R',row['directory'],row['namespace']]
    flags+=['-R',str(out.resolve()),'GeneratedAddFamilyProgramPrefix']
    root=memory.family.derived.controls.history.admission.observation.origin.ROOT;start=time.monotonic()
    baseline=out/'Baseline.v';baseline.write_text('Require Import Ex.External.CPUISAInstructionExecution.\nGoal True. idtac "ACCEPTANCE_ASSUMPTIONS". exact I. Qed.\nPrint Assumptions CPUISAInstructionExecution.token_execute.\n')
    bc,_=run_stage([str(root/'_opam/bin/coqc'),*flags,str(baseline.resolve())],out/'baseline.log',1200)
    allowed=parse_assumptions(bc.stdout)
    cc,ct=run_stage([str(root/'_opam/bin/coqc'),'-time',*flags,str(file.resolve())],out/'coqc.log',max(.1,1200-(time.monotonic()-start)))
    report=dict(accepted=False,coqc_exit=cc.returncode,coqc_timed_out=ct,baseline_exit=bc.returncode,
        source_sha256=memory.digest(source.encode()),ast_sha256=raw['source_sha256'],exports=exports,old_inv_read=False,
        static_program_certificate_has_no_CPU_correctness_claim=True,reset_to_arbitrary_bounded_family_cycles_proved=False,
        N_cycles_not_N_commits=True,not_a_fixed_trace=True,arbitrary_ADD_ADDI_parameters=True,
        sustained_progress_proved=False,infinite_itree_refinement_proved=False)
    if cc.returncode==0:
        axioms=audit_all_exports(cc.stdout.split('FAMILY_PROGRAM_AUDIT')[-1],len(exports));audit=bc.returncode==0 and not(axioms-allowed)and not(axioms-ALLOWED_AXIOMS)
        prefix=source[:source.index('Definition FamilyWord')]
        types=prefix+'Require Import GeneratedAddFamilyProgramPrefix.AddFamilyProgramPrefix.\nImport GeneratedAddFamilyProgramPrefix.AddFamilyProgramPrefix.\nSection OriginalISA.\n'
        types+=source.split('Section OriginalISA.\n',1)[1].split('Theorem actual_family_program_prefix',1)[0]
        headers={}
        for name in exports:
            match=re.search(r'(?:Theorem|Example) '+name+r'(?: ([A-Za-z0-9_ \n]+))?:(.*?)\n?Proof\.',source,re.S)
            if not match:raise ValueError('original public program type not found: '+name)
            args,statement=match.groups();args=args or '';headers[name]=memory.digest(match.group(0).removesuffix('Proof.').encode())
            types+=f'Definition checked_{name} {args}:{statement}\nProof. exact({name} {args}). Qed.\n'
        types+='End OriginalISA.\n';typefile=out/'TargetTypes.v';typefile.write_text(types)
        (out/'original-header-sha256.json').write_text(json.dumps(headers,indent=2)+'\n')
        tc,_=run_stage([str(root/'_opam/bin/coqc'),*flags,str(typefile.resolve())],out/'target-types.log',max(.1,1200-(time.monotonic()-start)))
        audit=audit and tc.returncode==0
        kk,kt=run_stage([str(root/'_opam/bin/coqchk'),'-silent',*flags,'-norec','GeneratedAddFamilyProgramPrefix.AddFamilyProgramPrefix','-norec','GeneratedAddFamilyProgramPrefix.TargetTypes'],out/'coqchk.log',max(.1,1200-(time.monotonic()-start)))
        report.update(accepted=audit and kk.returncode==0,coqchk_exit=kk.returncode,coqchk_timed_out=kt,target_types_exit=tc.returncode,
            assumptions=sorted(axioms),baseline_assumptions=sorted(allowed),assumptions_audit_passed=audit,
            reset_to_arbitrary_bounded_family_cycles_proved=audit and kk.returncode==0)
    report['seconds']=time.monotonic()-start
    if report['accepted']:report['object_sha256']=memory.digest(file.with_suffix('.vo').read_bytes())
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--cycle',required=True);p.add_argument('--output',required=True)
    a=p.parse_args();r=check(memory.family.inputs(),a.cycle,a.output)
    print(json.dumps(r,indent=2));raise SystemExit(0 if r['accepted']else 1)
