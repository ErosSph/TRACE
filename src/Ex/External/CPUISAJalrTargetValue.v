(** The original JALR target as an integer: (x + imm) mod 2^32 with bit 0 cleared.
    Pure ISA; connects [CPUISAJalrEffects.target] to the hardware's {sum[31:1],0}. *)
From Coq Require Import ZArith List Lia Bool.
Require Import Ex.External.CPUISAJalrEffects Ex.External.CPUISABranchFamilyEffects Ex.RvCore.FormalSpec
 coqutil.Word.Interface coqutil.Word.Properties coqutil.Word.Bitwidth coqutil.Map.Interface coqutil.Byte
 coqutil.Z.bitblast riscv.Utility.Utility.
Local Open Scope Z_scope.
Module CPUISAJalrTargetValue.
Section ISA.
Context {word:Interface.word 32}{BW:Bitwidth 32}{Registers:map.map Z word}{Mem:map.map word byte}
 {word_ok:word.ok word}{registers_ok:map.ok Registers}.

Lemma clear_bit0 y:0<=y<2^32 ->Z.land y(2^32-2)=Z.land y(Z.lnot 1).
Proof. intro HB;apply Z.bits_inj';intros n Hn.
 rewrite !Z.land_spec,Z.lnot_spec by lia.
 destruct(Z.ltb_spec n 32)as[H32|H32].
 - assert(Hm:Z.testbit(2^32-2)n=negb(Z.testbit 1 n)).
   { replace(2^32-2)with(Z.lnot 1 mod 2^32) by reflexivity.
     rewrite Z.mod_pow2_bits_low by lia;rewrite Z.lnot_spec by lia;reflexivity. }
   rewrite Hm;reflexivity.
 - assert(Hy:Z.testbit y n=false).
   { apply Z.bits_above_log2;[lia|].
     destruct(Z.eq_dec y 0)as[->|HNZ];[cbn;lia|].
     assert(Hl:Z.log2 y<32)by(apply(proj1(Z.log2_lt_pow2 y 32 ltac:(lia)));lia);lia. }
   rewrite Hy;reflexivity. Qed.

Theorem target_unsigned before rs1 imm:
 word.unsigned(CPUISAJalrEffects.target before rs1 imm)=
 Z.land((word.unsigned(CPUISABranchFamilyEffects.reg_word before rs1)+imm)mod 2^32)(Z.lnot 1).
Proof. unfold CPUISAJalrEffects.target.
 cbv beta iota zeta delta [Utility.and Utility.lnot Utility.ZToReg Utility.maxUnsigned MkMachineWidth.MachineWidth_XLEN xor].
 rewrite word.unsigned_and_nowrap,word.unsigned_xor_nowrap,word.unsigned_add,!word.unsigned_of_Z.
 unfold word.wrap.
 rewrite Z.add_mod_idemp_r by lia.
 change(Z.lxor(1 mod 2^32)((2^32-1)mod 2^32))with(2^32-2).
 apply clear_bit0;apply Z.mod_pos_bound;lia. Qed.
End ISA.
End CPUISAJalrTargetValue.
Print Assumptions CPUISAJalrTargetValue.target_unsigned.
Print Assumptions CPUISAJalrTargetValue.clear_bit0.
