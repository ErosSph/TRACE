(** Req39 projection-oriented executable trace over the real normalized
    CV32E40P. *)
From Coq Require Import ZArith List.
Require Import Lang.ExtendedSV.
Require Import Ex.Generated.CV32E40PExtendedAST.
Require Import Ex.External.CV32E40PReq38Phase.
Require Import Ex.External.CV32E40PReq38Clock.
Import ListNotations.
Import ExtendedSV CV32E40PExtendedAST CV32E40PReq38Phase.
Local Open Scope Z_scope.

Module CV32E40PReq39Trace.

  Definition drive (s : State) (writes : list (signal * Z)) : State :=
    fold_left (fun st xv => write_signal st (fst xv) (snd xv)) writes s.

  (** Deterministic one-entry OBI environment used by the refinement
      experiments.  A granted request is captured at the end of one cycle
      and answered in the next cycle.  This is an environment, not an
      internal ROM/RAM: only public top-level input ports are driven. *)
  Definition nop : Z := 19. (* addi x0,x0,0 = 0x00000013 *)

  Definition instruction_at (instruction address : Z) : Z :=
    if Z.eqb address 0 then instruction else nop.

  (** A byte-addressed instruction image.  Unlike [instruction_at], this
      interface can keep serving instructions after the first commit and is
      therefore suitable for next-commit/state-preservation proofs. *)
  Definition InstructionImage := list Z.

  Definition instruction_from_image (image : InstructionImage) (address : Z)
      : Z :=
    if andb (Z.leb 0 address) (Z.eqb (address mod 4) 0)
    then nth (Z.to_nat (address / 4)) image nop
    else nop.

  Record OBIDataRequest := {
    obi_data_address : Z;
    obi_data_write : bool;
    obi_data_byte_enable : Z;
    obi_data_write_data : Z
  }.

  Definition memory_read_word (word address : Z) : Z :=
    if Z.eqb (Z.land address (Z.lnot 3)) 0 then norm 32 word else 0.

  Definition store_lane (word be data lane : Z) : Z :=
    if Z.testbit be lane
    then write_slice word (8 * lane) 8 (Z.shiftr data (8 * lane))
    else word.

  Definition memory_store_word (word : Z) (request : OBIDataRequest) : Z :=
    if andb request.(obi_data_write)
         (Z.eqb (Z.land request.(obi_data_address) (Z.lnot 3)) 0)
    then store_lane
      (store_lane
        (store_lane
          (store_lane word request.(obi_data_byte_enable)
             request.(obi_data_write_data) 0)
          request.(obi_data_byte_enable) request.(obi_data_write_data) 1)
        request.(obi_data_byte_enable) request.(obi_data_write_data) 2)
      request.(obi_data_byte_enable) request.(obi_data_write_data) 3
    else word.

  Definition obi_ports (instruction memory_word : Z)
      (instruction_pending : option Z)
      (data_pending : option OBIDataRequest) (s : State) : State :=
    let instruction_valid :=
      match instruction_pending with Some _ => 1 | None => 0 end in
    let instruction_data :=
      match instruction_pending with
      | Some address => instruction_at instruction address
      | None => nop
      end in
    let data_valid := match data_pending with Some _ => 1 | None => 0 end in
    let data_read :=
      match data_pending with
      | Some request => memory_read_word memory_word request.(obi_data_address)
      | None => 0
      end in
    lfp_candidate cv32e40p_program
      (drive s [((9%nat), 1); ((10%nat), 0); ((11%nat), 0);
                ((12%nat), 0); ((13%nat), 0); ((14%nat), 0);
                ((15%nat), 0); ((17%nat), 1); ((18%nat), instruction_valid);
                ((20%nat), instruction_data);
                ((22%nat), 1); ((23%nat), data_valid);
                ((28%nat), data_read); ((29%nat), 0); ((32%nat), 0);
                ((36%nat), 1)]).

  Definition obi_ports_image (image : InstructionImage) (memory_word : Z)
      (instruction_pending : option Z)
      (data_pending : option OBIDataRequest) (s : State) : State :=
    let instruction_valid :=
      match instruction_pending with Some _ => 1 | None => 0 end in
    let instruction_data :=
      match instruction_pending with
      | Some address => instruction_from_image image address
      | None => nop
      end in
    let data_valid := match data_pending with Some _ => 1 | None => 0 end in
    let data_read :=
      match data_pending with
      | Some request => memory_read_word memory_word request.(obi_data_address)
      | None => 0
      end in
    lfp_candidate cv32e40p_program
      (drive s [((9%nat), 1); ((10%nat), 0); ((11%nat), 0);
                ((12%nat), 0); ((13%nat), 0); ((14%nat), 0);
                ((15%nat), 0); ((17%nat), 1); ((18%nat), instruction_valid);
                ((20%nat), instruction_data);
                ((22%nat), 1); ((23%nat), data_valid);
                ((28%nat), data_read); ((29%nat), 0); ((32%nat), 0);
                ((36%nat), 1)]).

  Definition addi_x1_x0_1 : Z := 1048723. (* 0x00100093 *)

  Record TraceState := {
    trace_rtl : State;
    trace_instruction_pending : option Z;
    trace_data_pending : option OBIDataRequest;
    trace_memory_word : Z
  }.

  Definition trace0_with_memory (memory_word : Z) : TraceState :=
    {| trace_rtl := CV32E40PReq38Clock.released;
       trace_instruction_pending := None;
       trace_data_pending := None;
       trace_memory_word := norm 32 memory_word |}.

  Definition trace0 : TraceState := trace0_with_memory 0.

  Definition clk_rise : Event :=
    {| changed_signal := 7%nat; old_value := 0; new_value := 1 |}.
  Definition clk_fall : Event :=
    {| changed_signal := 7%nat; old_value := 1; new_value := 0 |}.

  Definition capture_data_request (s : State) : option OBIDataRequest :=
    if Z.eqb (read_signal s 21%nat) 0 then None
    else Some
      {| obi_data_address := read_signal s 26%nat;
         obi_data_write := negb (Z.eqb (read_signal s 24%nat) 0);
         obi_data_byte_enable := read_signal s 25%nat;
         obi_data_write_data := read_signal s 27%nat |}.

  (** The four named boundaries below expose the real scheduler composition
      without exporting any evaluated 1800-signal post-state as a constant.
      Projection certificates can refer to one boundary and let the generic
      checker reduce only the queried cone. *)
  Definition environment_state (instruction : Z) (s : TraceState) : State :=
    obi_ports instruction s.(trace_memory_word)
      s.(trace_instruction_pending) s.(trace_data_pending) s.(trace_rtl).

  Definition rising_state (instruction : Z) (s : TraceState) : State :=
    PhaseSemantics cv32e40p_program clk_rise (environment_state instruction s).

  Definition falling_state (instruction : Z) (s : TraceState) : State :=
    PhaseSemantics cv32e40p_program clk_fall (rising_state instruction s).

  Definition settled_state (instruction : Z) (s : TraceState) : State :=
    lfp_candidate cv32e40p_program (falling_state instruction s).

  Definition full_cycle (instruction : Z) (s : TraceState) : TraceState :=
    let driven := environment_state instruction s in
    let settled := settled_state instruction s in
    let accepted_data := capture_data_request driven in
    {| trace_rtl := settled;
       trace_instruction_pending :=
         if Z.eqb (read_signal driven 16%nat) 0 then None
         else Some (read_signal driven 19%nat);
       trace_data_pending := accepted_data;
       trace_memory_word :=
         match accepted_data with
         | Some request => memory_store_word s.(trace_memory_word) request
         | None => s.(trace_memory_word)
         end |}.

  Definition environment_state_image (image : InstructionImage)
      (s : TraceState) : State :=
    obi_ports_image image s.(trace_memory_word)
      s.(trace_instruction_pending) s.(trace_data_pending) s.(trace_rtl).

  Definition rising_state_image (image : InstructionImage)
      (s : TraceState) : State :=
    PhaseSemantics cv32e40p_program clk_rise
      (environment_state_image image s).

  Definition falling_state_image (image : InstructionImage)
      (s : TraceState) : State :=
    PhaseSemantics cv32e40p_program clk_fall (rising_state_image image s).

  Definition settled_state_image (image : InstructionImage)
      (s : TraceState) : State :=
    lfp_candidate cv32e40p_program (falling_state_image image s).

  (** The real phase scheduler with a persistent instruction image.  The
      input state is used directly; in particular this operation performs no
      reset and does not reconstruct a zero fixture. *)
  Definition full_cycle_image (image : InstructionImage)
      (s : TraceState) : TraceState :=
    let driven := environment_state_image image s in
    let settled := settled_state_image image s in
    let accepted_data := capture_data_request driven in
    {| trace_rtl := settled;
       trace_instruction_pending :=
         if Z.eqb (read_signal driven 16%nat) 0 then None
         else Some (read_signal driven 19%nat);
       trace_data_pending := accepted_data;
       trace_memory_word :=
         match accepted_data with
         | Some request => memory_store_word s.(trace_memory_word) request
         | None => s.(trace_memory_word)
         end |}.

  Fixpoint cycles_image (image : InstructionImage) (n : nat)
      (s : TraceState) : TraceState :=
    match n with
    | O => s
    | S n' => cycles_image image n' (full_cycle_image image s)
    end.

  Fixpoint cycles (instruction : Z) (n : nat) (s : TraceState)
      : TraceState :=
    match n with O => s | S n' => cycles instruction n'
      (full_cycle instruction s) end.

  Definition next := full_cycle addi_x1_x0_1.
  Definition trace1 := next trace0.
  Definition trace2 := next trace1.
  Definition trace3 := next trace2.
  Definition trace4 := next trace3.
  Definition trace5 := next trace4.
  Definition trace6 := next trace5.
  Definition trace7 := next trace6.
  Definition trace8 := next trace7.
  Definition trace9 := next trace8.
  Definition trace10 := next trace9.

  Definition observations (s : State) : list Z :=
    map (read_signal s)
      ([7; 8; 16; 19; 20; 21; 24; 26; 27; 107; 120; 121; 122; 134;
       185; 186; 187; 188; 189; 192; 193; 194; 195; 222; 260; 284;
       336; 340; 341; 374; 519; 565; 566; 581; 586; 588; 596; 597;
       688; 689; 690; 691; 693; 694; 695; 697; 772; 773; 774; 775;
       810; 876; 877; 884; 885; 902; 1256; 1257; 1258; 1259; 1262;
       1263; 1264; 1265; 1266; 1267; 1268; 1269; 1278;
       287; 288; 289; 290; 291; 292; 293; 294; 295; 296; 297; 298;
       299; 300; 301; 302; 303; 304; 305; 306; 307; 308; 309; 310;
       311; 312; 313; 314]%nat).

  Definition selected_count (s : State) (ev : Event) : nat :=
    List.length (selected_on_transition cv32e40p_program s
      (phase_driven_state cv32e40p_program ev s)).

  Definition architectural_observations (s : State) : list Z :=
    map (read_signal s)
      ([16; 19; 107; 120; 121; 122; 134; 185; 186; 187; 188; 189;
        192; 193; 194; 195; 222; 260; 565; 566; 581; 586; 588; 596;
        597; 688; 689; 690; 691; 692; 693; 694; 695; 697; 772; 773;
        774; 775; 810; 876; 877; 884; 894; 897; 902; 906; 907; 1256;
        1257; 1258; 1259; 1262; 1263; 1264; 1265; 1266; 1267; 1268;
        1269; 1278; 718; 720; 721; 725]%nat).

  Definition short_observations (s : State) : list Z :=
    map (read_signal s)
      ([16; 19; 107; 120; 121; 122; 134; 187; 188; 189; 192; 193;
        194; 195; 222; 260; 581; 586; 597; 688; 689; 690; 691; 692;
        693; 694; 695; 697; 772; 774; 810; 876; 877; 884; 902; 1278;
        718; 720; 721; 725]%nat).

  Fixpoint collect (n : nat) (s : TraceState) : list (list Z) :=
    match n with
    | O => [short_observations s.(trace_rtl)]
    | S n' => short_observations s.(trace_rtl) :: collect n' (next s)
    end.

  Fixpoint collect_for (instruction : Z) (projection : State -> list Z)
      (n : nat) (s : TraceState) : list (list Z) :=
    match n with
    | O => [projection s.(trace_rtl)]
    | S n' => projection s.(trace_rtl) ::
        collect_for instruction projection n' (full_cycle instruction s)
    end.

  Definition trace_at (instruction data : Z) (n : nat) : TraceState :=
    cycles instruction n (trace0_with_memory data).

  Definition rtl_at (instruction data : Z) (n : nat) : State :=
    (trace_at instruction data n).(trace_rtl).

  Definition rf_register (s : State) (reg : nat) : Z :=
    norm 32 (Z.shiftr (read_signal s 902%nat) (Z.of_nat (32 * reg))).

  (** Checked provenance:
      [341] = cv32e40p_top.core_i.if_stage_i.pc_id_o.
      Signal [581] is only the combinationally connected
      id_stage_i.pc_id_i alias used by [issue_projection]. *)
  Definition architectural_pc_signal : signal := 341%nat.

  Definition issue_projection (s : State) : list Z :=
    map (read_signal s)
      ([581; 586; 718; 720; 721; 725; 877]%nat).

  Definition execute_projection (s : State) : list Z :=
    map (read_signal s)
      ([192; 193; 194; 195; 260; 692; 693; 694; 695; 697; 1278]%nat).

  Definition writeback_projection (s : State) : list Z :=
    [rf_register s 0; rf_register s 1; read_signal s 21%nat;
     read_signal s 24%nat; read_signal s 581%nat].

  (** A single state-threaded computation; the large CPU state is never
      exported or materialised as a proof constant. *)
  Definition first_commit_bundle (instruction data : Z)
      : list Z * list Z * list Z :=
    let t4 := trace_at instruction data 4 in
    let t5 := full_cycle instruction t4 in
    let t6 := full_cycle instruction t5 in
    (issue_projection t4.(trace_rtl),
     execute_projection t5.(trace_rtl),
     writeback_projection t6.(trace_rtl) ++ [t6.(trace_memory_word)]).

End CV32E40PReq39Trace.
