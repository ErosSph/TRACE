(**
    Architectural-state relation for the repaired bzeeno RV32I pipeline.

    This is deliberately separate from [BzeenoRefinement].  The latter only
    names the commit-PC observation, whereas an ISA refinement has to relate
    every architectural component that an RV32I instruction can observe or
    modify.  The three concrete storage relations below use the physical
    organization of the imported RTL:

    - instruction ROM: 101 32-bit words, indexed by [pc[31:2]];
    - data RAM: 128 8-bit bytes, indexed by a byte address;
    - register file: 32 32-bit cells, with x0 hard-wired to zero at reads.

    The definitions are intentionally extensional.  A theorem can add another
    architecturally visible component by conjoining another relation; it must
    not silently compare only the commit PC.
 *)
From Coq Require Import ZArith.BinInt Lists.List Lia.
Require Import Lib.Lib. Import SZNotations.
Require Import Ex.RvCore.FormalSpec.
Require Import Ex.External.BzeenoCPU.
Require Import Ex.External.BzeenoPipeline.
Require Import Ex.External.BzeenoTopState.
Require Import coqutil.Byte coqutil.Datatypes.HList coqutil.Word.Interface coqutil.Word.Bitwidth coqutil.Word.Properties
               coqutil.Map.Interface.
Require Import riscv.Spec.Machine riscv.Spec.Decode.
Require Import riscv.Utility.MkMachineWidth riscv.Utility.Utility.

Import ListNotations.
Local Open Scope Z_scope.

#[local] Existing Instance SZ_sz_ops.
#[local] Existing Instance hmap_array_ops.

Module BzeenoFormalSim.
  Section RV32I.
    Context {word : Interface.word 32} {BW : Bitwidth 32} {MW : MachineWidth word}.
    Context {Registers : map.map Decode.Register word} {Mem : map.map word byte}.

    (** A concrete RTL array cell is either an explicit normalized bit-vector
        or an absent sparse-map cell.  In this framework an absent array cell
        reads as zero, which is precisely how the all-zero power-on RAM/RF
        images are represented. *)
    Definition cell32 (v : hmap) : Prop :=
      v = HMapEmpty \/ exists z, v = HMapBits #{z, 32, false}.

    Definition cell8 (v : hmap) : Prop :=
      v = HMapEmpty \/ exists z, v = HMapBits #{z, 8, false}.

    (** ROM is related word-for-word only over the physically implemented
        address range.  The premise [unsigned pc = 4 * word_index] matches
        the RTL expression [pc[31:2]], and makes the byte addressing used by
        [FormalSpec] explicit. *)
    Definition rom_related
        (formal_rom : Mem) (rtl_rom : list (Z * hmap)) : Prop :=
      forall (pc : word) (word_index : Z),
        word.unsigned pc = 4 * word_index ->
        (0 <= word_index < 101)%Z ->
        cell32 (hselectA rtl_rom word_index) /\
        exists tup,
          Memory.load_bytes 4 formal_rom pc = Some tup /\
          LittleEndian.combine 4 tup =
            szNormZ (hbits (hselectA rtl_rom word_index)).

    (** RAM is byte-related, rather than word-related.  This is the essential
        relation for SB/SH: the other bytes of a word remain independently
        observable after a partial store. *)
    Definition ram_related
        (formal_ram : Mem) (rtl_ram : list (Z * hmap)) : Prop :=
      forall (addr : word),
        (0 <= word.unsigned addr < 128)%Z ->
        cell8 (hselectA rtl_ram (word.unsigned addr)) /\
        exists tup,
          Memory.load_bytes 1 formal_ram addr = Some tup /\
          LittleEndian.combine 1 tup =
            szNormZ (hbits (hselectA rtl_ram (word.unsigned addr))).

    Definition formal_reg_value (formal_rf : Registers) (reg : Z) : Z :=
      match map.get formal_rf reg with
      | Some v => word.unsigned v
      | None => 0
      end.

    (** [rf_related] records both aspects of the RISC-V x0 rule: the
        implementation's physical zero cell is zero, and every nonzero
        architectural register has the same unsigned 32-bit value. *)
    Definition rf_related
        (formal_rf : Registers) (rtl_rf : list (Z * hmap)) : Prop :=
      cell32 (hselectA rtl_rf 0) /\
      szNormZ (hbits (hselectA rtl_rf 0)) = 0 /\
      forall reg,
        (0 < reg < 32)%Z ->
        cell32 (hselectA rtl_rf reg) /\
        formal_reg_value formal_rf reg =
          szNormZ (hbits (hselectA rtl_rf reg)).

    (** A one-byte view is convenient for proving partial-store preservation.
        It is stronger than merely observing aligned 32-bit loads: each of
        the four constituent bytes remains related independently. *)
    Definition formal_byte_value (formal_ram : Mem) (addr : word) : Z :=
      match map.get formal_ram addr with
      | Some b => byte.unsigned b
      | None => 0
      end.

    Definition ram_cells_related
        (formal_ram : Mem) (rtl_ram : list (Z * hmap)) : Prop :=
      forall addr,
        (0 <= word.unsigned addr < 128)%Z ->
        cell8 (hselectA rtl_ram (word.unsigned addr)) /\
        formal_byte_value formal_ram addr =
          szNormZ (hbits (hselectA rtl_ram (word.unsigned addr))).

    Definition rtl_store_byte
        (rtl_ram : list (Z * hmap)) (addr : word) (b : byte) : list (Z * hmap) :=
      hbinUArr hupds rtl_ram
        [(word.unsigned addr, HMapBits #{byte.unsigned b, 8, false})].

    Fixpoint formal_store_bytes (formal_ram : Mem) (addr : word)
        (bytes : list byte) : Mem :=
      match bytes with
      | [] => formal_ram
      | b :: bytes' =>
          formal_store_bytes (map.put formal_ram addr b)
            (word.add addr (word.of_Z 1)) bytes'
      end.

    Fixpoint rtl_store_bytes (rtl_ram : list (Z * hmap)) (addr : word)
        (bytes : list byte) : list (Z * hmap) :=
      match bytes with
      | [] => rtl_ram
      | b :: bytes' =>
          rtl_store_bytes (rtl_store_byte rtl_ram addr b)
            (word.add addr (word.of_Z 1)) bytes'
      end.

    Definition rtl_write_register
        (rtl_rf : list (Z * hmap)) (rd : Z) (value : SZ) : list (Z * hmap) :=
      hbinUArr hupds rtl_rf [(rd, HMapBits value)].

    (** The complete implementation-to-ISA state invariant.  The pipeline
        control invariant is left as a parameter because it is design
        specific (valid bits, forwarding, stalls, and flushes).  In contrast,
        ROM/RAM/RF are required for every RV32I proof of this core. *)
    Record ArchStateRelated
        (pipeline_inv : BzeenoTopState.Flops -> FormalSpec.State -> Prop)
        (impl : BzeenoCPU.Flops) (spec : FormalSpec.State) : Prop := {
      arch_pipeline : pipeline_inv (BzeenoCPU.core_v impl) spec;
      arch_rom : rom_related (getInstMem spec)
                    (BzeenoPipeline.InstructionMem.rom_v (BzeenoCPU.imem_v impl));
      arch_ram : ram_related (getDataMem spec)
                    (BzeenoPipeline.DataMem.ram_v (BzeenoCPU.dmem_v impl));
      arch_ram_cells : ram_cells_related (getDataMem spec)
                    (BzeenoPipeline.DataMem.ram_v (BzeenoCPU.dmem_v impl));
      arch_rf : rf_related (getRegs spec)
                  (BzeenoPipeline.RegFile.regs_v
                    (BzeenoTopState.rf_v (BzeenoCPU.core_v impl)));
    }.

    (** This is the single observation equation used when a valid WB entry
        is emitted.  The RAM/RF/ROM clauses above remain live across stutter
        cycles and are not discarded at the observation boundary. *)
    Definition commit_related
        (impl : BzeenoCPU.Flops) (spec : FormalSpec.State) : Prop :=
      BzeenoTopState.commit_vld (BzeenoCPU.core_v impl) <> #{1, 1, false} \/
      word.unsigned (getPc spec) =
        szNormZ (BzeenoTopState.commit_pc (BzeenoCPU.core_v impl)).

    Lemma arch_rom_component pipeline_inv impl spec
        (H : ArchStateRelated pipeline_inv impl spec) :
      rom_related (getInstMem spec)
        (BzeenoPipeline.InstructionMem.rom_v (BzeenoCPU.imem_v impl)).
    Proof. exact (arch_rom _ _ _ H). Qed.

    Lemma arch_ram_component pipeline_inv impl spec
        (H : ArchStateRelated pipeline_inv impl spec) :
      ram_related (getDataMem spec)
        (BzeenoPipeline.DataMem.ram_v (BzeenoCPU.dmem_v impl)).
    Proof. exact (arch_ram _ _ _ H). Qed.

    Lemma arch_rf_component pipeline_inv impl spec
        (H : ArchStateRelated pipeline_inv impl spec) :
      rf_related (getRegs spec)
        (BzeenoPipeline.RegFile.regs_v
          (BzeenoTopState.rf_v (BzeenoCPU.core_v impl))).
    Proof. exact (arch_rf _ _ _ H). Qed.

    Lemma arch_x0_is_zero pipeline_inv impl spec
        (H : ArchStateRelated pipeline_inv impl spec) :
      szNormZ (hbits
        (hselectA (BzeenoPipeline.RegFile.regs_v
          (BzeenoTopState.rf_v (BzeenoCPU.core_v impl))) 0)) = 0.
    Proof. exact (proj1 (proj2 (arch_rf_component _ _ _ H))). Qed.

    Context {mem_ok : map.ok Mem} {word_ok : word.ok word}
            {registers_ok : map.ok Registers}.

    Definition program_rom (program : list (Z * Z)) : list (Z * hmap) :=
      List.map (fun iv => (fst iv, HMapBits #{snd iv, 32, false})) program.

    Lemma program_rom_cells program index :
      cell32 (hselectA (program_rom program) index).
    Proof.
      induction program as [|[i v] program IH]; cbn.
      - left. reflexivity.
      - destruct (index =? i) eqn: E.
        + right. eexists. reflexivity.
        + exact IH.
    Qed.

    Definition rom_values_related
        (formal_rom : Mem) (rtl_rom : list (Z * hmap)) : Prop :=
      forall (pc : word) (word_index : Z),
        word.unsigned pc = 4 * word_index ->
        exists tup,
          Memory.load_bytes 4 formal_rom pc = Some tup /\
          LittleEndian.combine 4 tup =
            szNormZ (hbits (hselectA rtl_rom word_index)).

    (** Keep [4 * index] opaque while exposing the byte stores.  This avoids
        the syntactic normalization of multiplication that otherwise hides
        the common address from [map.get_put_same]. *)
    Lemma formal_initial_rom_values_related initial_imem
        (IMEM_OK : List.Forall (fun iv => (0 <= fst iv < 2 ^ 30)%Z) initial_imem) :
      rom_values_related (FormalSpec.formal_initial_imem initial_imem)
        (program_rom initial_imem).
    Proof.
      unfold rom_values_related, program_rom. intros access_w access_ind H.
      induction initial_imem as [|[a val] imem' IH].
      - assert (FormalSpec.formal_initial_imem nil = FormalSpec.zeroed) as -> by reflexivity.
        epose proof (FormalSpec.zeroed_load_bytes (Mem := Mem) 4 access_w) as (? & -> & Hcomb).
        eexists. split; [reflexivity|]. cbn. exact Hcomb.
      - destruct IH as (tup_prev & Hprev_acc & Harr_select).
        { apply Forall_inv_tail in IMEM_OK. exact IMEM_OK. }
        unfold FormalSpec.formal_initial_imem. cbn -[Z.mul].
        set (fold_right _ _ _) as prev_mem.
        replace (FormalSpec.formal_initial_imem _) with prev_mem in Hprev_acc by reflexivity.
        clearbody prev_mem.
        destruct (Z.eq_dec a access_ind) as [-> | NEQ].
        + exists (LittleEndian.split 4 val).
          unfold Memory.load_bytes, Memory.unchecked_store_bytes, map.getmany_of_tuple, map.putmany_of_tuple.
          cbn -[Z.mul].
          assert (word.of_Z (4 * access_ind) = access_w) as ->.
          { apply word.unsigned_inj. rewrite <- H. rewrite word.of_Z_unsigned. reflexivity. }
          progress repeat (rewrite map.get_put_same || rewrite map.get_put_diff).
          2-7:
            clear -word_ok; intros Heq;
            apply f_equal with (f := word.unsigned), Zeq_minus, f_equal with (f := word.wrap) in Heq;
            rewrite !word.unsigned_add, !word.unsigned_of_Z in Heq;
            unfold word.wrap in Heq;
            rewrite_strat (bottomup repeat choice Z.add_mod_idemp_l Z.add_mod_idemp_r Zdiv.Zminus_mod_idemp_r Zdiv.Zminus_mod_idemp_l) in Heq; [|lia..];
            match type of Heq with | (?x mod _ = _) => first [replace x with 1 in Heq by lia| replace x with 2 in Heq by lia| replace x with 3 in Heq by lia] end;
            discriminate Heq.
          split; [reflexivity|].
          rewrite Z.eqb_refl. rewrite LittleEndian.combine_split. reflexivity.
        + exists tup_prev.
          apply Forall_inv in IMEM_OK. simpl in IMEM_OK.
          split.
          * unfold Memory.load_bytes, map.getmany_of_tuple. cbn -[Z.mul].
            assert (access_w <> word.of_Z (4 * a)) as Haccess_w.
            { intros ->. rewrite word.unsigned_of_Z in H. unfold word.wrap in H.
              rewrite Z.mod_small in H; lia. }
            clear -Haccess_w H word_ok mem_ok IMEM_OK Hprev_acc.
            rewrite 16!map.get_put_diff.
            17: { assumption. }
            2, 7, 12: intros Heq;
              repeat (apply f_equal with (f := fun x => word.sub x (word.of_Z 1)) in Heq;
                      rewrite !word.word_sub_add_l_same_r in Heq);
              contradiction.
            2-13:
              intros Heq; apply f_equal with (f := fun x => word.unsigned x mod 4) in Heq;
              rewrite ?word.unsigned_add, ?word.unsigned_of_Z, H in Heq;
              unfold word.wrap in Heq;
              rewrite_strat (bottomup repeat choice Z.add_mod_idemp_l Z.add_mod_idemp_r) in Heq; [|lia..];
              repeat (rewrite <- Znumtheory.Zmod_div_mod in Heq; [|lia..| exists (2^30); lia]);
              rewrite !Z.add_comm with (m := 1), ?Z.add_assoc, 2!Z.mul_comm with (n := 4), ?Z.mod_mul, ?Zdiv.Z_mod_plus_full in Heq by lia;
              discriminate Heq.
            exact Hprev_acc.
          * rewrite <- Z.eqb_neq, Z.eqb_sym in NEQ. rewrite NEQ. exact Harr_select.
    Qed.

    Lemma formal_initial_rom_related initial_imem
        (IMEM_OK : List.Forall (fun iv => (0 <= fst iv < 101)%Z) initial_imem) :
      rom_related (FormalSpec.formal_initial_imem initial_imem)
        (program_rom initial_imem).
    Proof.
      intros pc index Hpc _. split.
      - apply program_rom_cells.
      - assert (IMEM_OK32 : List.Forall
            (fun iv => (0 <= fst iv < 2 ^ 30)%Z) initial_imem).
        { apply Forall_impl with (P := fun iv => (0 <= fst iv < 101)%Z); auto.
          intros [i v] Hi. lia. }
        exact (formal_initial_rom_values_related initial_imem IMEM_OK32 pc index Hpc).
    Qed.

    (** ROM has no sequential assignment in the imported RTL.  Its all-zero
        image is the first checked initialization case; the nonzero program
        image uses [program_rom] above and is the remaining byte/word
        initialization lemma needed by the final generic theorem. *)
    Lemma zeroed_rom_related :
      rom_related (FormalSpec.zeroed (Mem := Mem)) [].
    Proof.
      intros pc index _ _. split; [left; reflexivity|].
      destruct (FormalSpec.zeroed_load_bytes (Mem := Mem) 4 pc)
        as (tup & Hload & Hvalue).
      exists tup. split; [exact Hload|]. cbn. exact Hvalue.
    Qed.

    (** A byte store changes exactly one logical RAM byte.  This lemma is the
        storage part of the SB proof; SH and SW follow by applying it to two
        or four consecutive byte updates. *)
    Lemma ram_cells_store_byte_related formal_ram rtl_ram addr b
        (PREV : ram_cells_related formal_ram rtl_ram) :
      ram_cells_related (map.put formal_ram addr b)
        (rtl_store_byte rtl_ram addr b).
    Proof.
      intros addr' RANGE.
      destruct (Z.eq_dec (word.unsigned addr') (word.unsigned addr)) as [EQ | NEQ].
      - assert (addr' = addr) as -> by (apply word.unsigned_inj; exact EQ).
        split.
        + unfold rtl_store_byte. right. eexists.
          rewrite hselectA_single_upd_bits. reflexivity.
        + unfold formal_byte_value, rtl_store_byte.
          rewrite map.get_put_same, hselectA_single_upd_bits.
          unfold szNormZ. cbn. symmetry. apply Z.mod_small.
          apply byte.unsigned_range.
      - specialize (PREV addr' RANGE) as (HCELL & HVAL).
        split.
        + unfold rtl_store_byte.
          rewrite hselectA_single_upd_neq; [exact HCELL|].
          intro E. apply NEQ. symmetry. exact E.
        + unfold formal_byte_value, rtl_store_byte in *.
          rewrite map.get_put_diff.
          * rewrite hselectA_single_upd_neq; [exact HVAL|].
            intro E. apply NEQ. symmetry. exact E.
          * intro E. apply NEQ. apply f_equal with (f := word.unsigned) in E.
            exact E.
    Qed.

    (** Instantiating this theorem with a two- or four-byte little-endian
        list gives the SH or SW storage preservation obligation. *)
    Lemma ram_cells_store_bytes_related formal_ram rtl_ram addr bytes
        (PREV : ram_cells_related formal_ram rtl_ram) :
      ram_cells_related (formal_store_bytes formal_ram addr bytes)
        (rtl_store_bytes rtl_ram addr bytes).
    Proof.
      revert formal_ram rtl_ram addr PREV.
      induction bytes as [|b bytes IH]; intros formal_ram rtl_ram addr PREV; cbn.
      - exact PREV.
      - apply IH. apply ram_cells_store_byte_related. exact PREV.
    Qed.

    (** The observable one-byte RAM relation is preserved by the same
        update.  Unlike [ram_cells_related], this formulation goes through
        [Memory.load_bytes], so it is the clause used by the RV32I load and
        store semantics. *)
    Lemma ram_store_byte_related formal_ram rtl_ram addr b
        (PREV : ram_related formal_ram rtl_ram) :
      ram_related (map.put formal_ram addr b)
        (rtl_store_byte rtl_ram addr b).
    Proof.
      intros addr' RANGE.
      destruct (Z.eq_dec (word.unsigned addr') (word.unsigned addr)) as [EQ | NEQ].
      - assert (addr' = addr) as -> by (apply word.unsigned_inj; exact EQ).
        split.
        + unfold rtl_store_byte. right. eexists.
          rewrite hselectA_single_upd_bits. reflexivity.
        + exists (PrimitivePair.pair.mk b tt).
          unfold Memory.load_bytes, map.getmany_of_tuple. cbn.
          rewrite map.get_put_same. split; [reflexivity|].
          unfold rtl_store_byte. rewrite hselectA_single_upd_bits.
          assert (LittleEndian.combine 1 (PrimitivePair.pair.mk b tt) =
            byte.unsigned b) as HBYTE.
          { cbv [LittleEndian.combine_deprecated
                   PrimitivePair.pair._1 PrimitivePair.pair._2].
            rewrite Z.lor_0_r. reflexivity. }
          rewrite HBYTE.
          unfold szNormZ. cbn. symmetry.
          apply Z.mod_small. apply byte.unsigned_range.
      - specialize (PREV addr' RANGE) as (HCELL & tup & HLOAD & HCOMB).
        split.
        + unfold rtl_store_byte.
          rewrite hselectA_single_upd_neq; [exact HCELL|].
          intro E. apply NEQ. symmetry. exact E.
        + exists tup. split.
          * unfold Memory.load_bytes, map.getmany_of_tuple in HLOAD |- *. cbn in *.
            rewrite map.get_put_diff; [exact HLOAD|].
            intro E. apply NEQ. apply f_equal with (f := word.unsigned) in E.
            exact E.
          * unfold rtl_store_byte.
            rewrite hselectA_single_upd_neq; [exact HCOMB|].
            intro E. apply NEQ. symmetry. exact E.
    Qed.

    (** SB, SH, and SW are represented by lists of respectively one, two,
        and four little-endian bytes. *)
    Lemma ram_store_bytes_related formal_ram rtl_ram addr bytes
        (PREV : ram_related formal_ram rtl_ram) :
      ram_related (formal_store_bytes formal_ram addr bytes)
        (rtl_store_bytes rtl_ram addr bytes).
    Proof.
      revert formal_ram rtl_ram addr PREV.
      induction bytes as [|b bytes IH]; intros formal_ram rtl_ram addr PREV; cbn.
      - exact PREV.
      - apply IH. apply ram_store_byte_related. exact PREV.
    Qed.

    (** A nonzero register-file write preserves the ISA/RF relation.  The
        [VALUE] premise is exactly the arithmetic side condition discharged
        when connecting the MEM/WB data path to [Machine.setRegister]. *)
    Lemma rf_write_register_related formal_rf rtl_rf rd w value z
        (RD_RANGE : (0 < rd < 32)%Z)
        (VALUE_FORMAT : value = #{z, 32, false})
        (VALUE : word.unsigned w = szNormZ value)
        (PREV : rf_related formal_rf rtl_rf) :
      rf_related (map.put formal_rf rd w)
        (rtl_write_register rtl_rf rd value).
    Proof.
      destruct PREV as (HX0CELL & HX0 & HPREV).
      split.
      - unfold rtl_write_register.
        rewrite hselectA_single_upd_neq; [exact HX0CELL|lia].
      - split.
        + unfold rtl_write_register.
          rewrite hselectA_single_upd_neq; [exact HX0|lia].
        + intros reg REG_RANGE.
          destruct (Z.eq_dec reg rd) as [-> | NEQ].
          * split.
            -- unfold rtl_write_register. right. exists z.
               rewrite hselectA_single_upd_bits. now rewrite VALUE_FORMAT.
            -- unfold formal_reg_value, rtl_write_register.
               rewrite map.get_put_same, hselectA_single_upd_bits.
               exact VALUE.
          * specialize (HPREV reg REG_RANGE) as (HCELL & HVAL).
            split.
            -- unfold rtl_write_register.
               rewrite hselectA_single_upd_neq; [exact HCELL|].
               intro E. apply NEQ. symmetry. exact E.
            -- unfold formal_reg_value, rtl_write_register in *.
               rewrite map.get_put_diff.
               ++ rewrite hselectA_single_upd_neq; [exact HVAL|].
                  intro E. apply NEQ. symmetry. exact E.
               ++ exact NEQ.
    Qed.

    (** The formal ISA starts with a byte-addressable all-zero data memory.
        The RTL RAM starts as the sparse empty image, whose missing cells read
        as zero.  This is an actual base-case proof for the RAM relation, not
        a reset assumption hidden in the final refinement theorem. *)
    Lemma zeroed_ram_related :
      ram_related (FormalSpec.zeroed (Mem := Mem)) [].
    Proof.
      intros addr _. split.
      - left. reflexivity.
      - destruct (FormalSpec.zeroed_load_bytes (Mem := Mem) 1 addr)
          as (tup & Hload & Hvalue).
        exists tup. split; [exact Hload|].
        cbn. exact Hvalue.
    Qed.

    (** The cell-wise form of the same reset fact.  This is kept separate
        from [zeroed_ram_related]: the latter is used by loads, while this
        stronger pointwise statement is the induction base for SB/SH/SW
        preservation. *)
    Lemma zeroed_ram_cells_related :
      ram_cells_related (FormalSpec.zeroed (Mem := Mem)) [].
    Proof.
      intros addr _. split; [left; reflexivity|].
      unfold formal_byte_value. rewrite FormalSpec.zeroed_access. reflexivity.
    Qed.

    (** The ISA register map is empty at reset (therefore every read returns
        zero), and the RTL sparse register array has the same interpretation.
        x0 is stated explicitly because it is an ISA invariant even after
        arbitrary later write attempts. *)
    Lemma empty_rf_related :
      rf_related (map.empty : Registers) [].
    Proof.
      split; [left; reflexivity|]. split; [reflexivity|].
      intros reg _. split; [left; reflexivity|].
      unfold formal_reg_value. rewrite map.get_empty. reflexivity.
    Qed.
  End RV32I.
End BzeenoFormalSim.
