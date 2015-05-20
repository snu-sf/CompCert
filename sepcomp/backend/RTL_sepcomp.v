Require Import Coqlib.
Require Import Maps.
Require Import Integers.
Require Import Values.
Require Import Memory.
Require Import Events.
Require Import Op.
Require Import Registers.
Require Import RTL.
Require Import sflib.

Set Implicit Arguments.

Lemma inject_separated_refl F m tm:
  inject_separated F F m tm.
Proof. ii. congruence. Qed.

Lemma val_inject_set_reg:
  forall F rs rs' r v v',
  (forall r', val_inject F rs # r' rs' # r') ->
  val_inject F v v' ->
  forall r', val_inject F (rs#r <- v) # r' (rs'#r <- v') # r'.
Proof.
  intros. rewrite ? Regmap.gsspec. destruct (peq r' r); auto.
Qed.

Lemma val_inject_init_regs F args args' params
      (ARGS: val_list_inject F args args'):
  forall r, val_inject F (init_regs args params) # r (init_regs args' params) # r.
Proof.
  revert args args' ARGS. induction params; simpl; intros.
  - rewrite ? Regmap.gi. auto.
  - inv ARGS.
    + rewrite ? Regmap.gi. auto.
    + apply val_inject_set_reg; auto.
Qed.

Definition is_normal (s:state): bool :=
  match s with
    | State _ f _ pc _ _ =>
      match (fn_code f)!pc with
        | None => false
        | Some(Icall _ _ _ _ _) => false
        | Some(Itailcall _ _ _) => false
        | Some(Ireturn _) => false
        | _ => true
      end
    | _ => false
  end.

Lemma is_normal_step ge s f sp pc1 rs1 m1 s2 tr
      (NORMAL: is_normal (State s f sp pc1 rs1 m1))
      (STEP: step ge (State s f sp pc1 rs1 m1) tr s2):
  exists pc2 rs2 m2,
    <<S2: s2 = State s f sp pc2 rs2 m2>> /\
    <<VALID: forall b (V: Mem.valid_block m1 b), Mem.valid_block m2 b>> /\
    <<PERM: forall b ofs p (V: Mem.valid_block m1 b) (P: Mem.perm m2 b ofs Max p), Mem.perm m1 b ofs Max p>>.
Proof.
  simpl in *. destruct (fn_code f) ! pc1 as [[]|] eqn:X; clarify; inv STEP; clarify; eexists; eexists; eexists; splits; eauto.
  - destruct a0; inv H9. unfold Mem.valid_block. erewrite <- Mem.nextblock_store; eauto.
  - destruct a0; inv H9. intros. eapply Mem.perm_store_2; eauto.
  - intros. eapply external_call_valid_block; eauto.
  - intros. eapply external_call_max_perm; eauto.
Qed.

Lemma is_normal_steps
      ge s f sp pc1 rs1 m1 pc2 rs2 m2 tr
      tge ts tsp trs1 tm1
      F1
      (NORMAL1: is_normal (State s f (Vptr sp Int.zero) pc1 rs1 m1))
      (STEP: step ge (State s f (Vptr sp Int.zero) pc1 rs1 m1) tr (State s f (Vptr sp Int.zero) pc2 rs2 m2))
      (SP: F1 sp = Some(tsp, 0))
      (PRES1: meminj_preserves_globals ge F1)
      (REGSET1: forall r, val_inject F1 rs1#r trs1#r)
      (MEM1: Mem.inject F1 m1 tm1):
  exists F2 trs2 tm2,
    <<TSTEP: step tge (State ts f (Vptr tsp Int.zero) pc1 trs1 tm1) tr (State ts f (Vptr tsp Int.zero) pc2 trs2 tm2)>> /\
    <<MAXPERM: forall b ofs p, Mem.valid_block m1 b -> Mem.perm m2 b ofs Max p -> Mem.perm m1 b ofs Max p>> /\
    <<MAXPERM': forall b ofs p, Mem.valid_block tm1 b -> Mem.perm tm2 b ofs Max p -> Mem.perm tm1 b ofs Max p>> /\
    <<UNCHANGED: Mem.unchanged_on (loc_out_of_reach F1 m1) tm1 tm2>> /\
    <<REGSET2: forall r, val_inject F2 rs2#r trs2#r>> /\
    <<MEM2: Mem.inject F2 m2 tm2>> /\
    <<INCR: inject_incr F1 F2>> /\
    <<SEP: inject_separated F1 F2 m1 tm1>>.
Proof.
  simpl in *. destruct (fn_code f) ! pc1 as [[]|] eqn:X; clarify; inv STEP; clarify.
  - eexists. eexists. eexists. splits; eauto.
    + apply exec_Inop; eauto.
    + apply Mem.unchanged_on_refl.
    + apply inject_separated_refl.
  - exploit eval_operation_inject; try apply H10; eauto.
    { instantiate (1 := trs1 ## l). admit. }
    intro. des.
    eexists. eexists. eexists. splits; eauto.
    + eapply exec_Iop; eauto.
      instantiate (1 := v2). admit.
    + apply Mem.unchanged_on_refl.
    + apply val_inject_set_reg; auto.
    + apply inject_separated_refl.
  - exploit eval_addressing_inject; try apply H10; eauto.
    { instantiate (1 := trs1 ## l). admit. }
    intro. des.
    exploit Mem.loadv_inject; eauto.
    intro. des.
    eexists. eexists. eexists. splits; eauto.
    + eapply exec_Iload; eauto.
      admit.
    + apply Mem.unchanged_on_refl.
    + apply val_inject_set_reg; auto.
    + apply inject_separated_refl.
  - exploit eval_addressing_inject; try apply H10; eauto.
    { instantiate (1 := trs1 ## l). admit. }
    intro. des.
    exploit Mem.storev_mapped_inject; eauto.
    intro. des.
    eexists. eexists. exists n2. splits; eauto.
    + eapply exec_Istore; eauto.
      admit.
    + admit. (* perm? *)
    + admit. (* perm? *)
    + admit. (* unchanged_on loc_out_of_reach *)
    + apply inject_separated_refl.
  - admit. (* external call *)
  - exploit eval_condition_inject; try apply H10; eauto.
    { instantiate (1 := trs1 ## l). admit. }
    intro.
    eexists. eexists. eexists. splits; eauto.
    + eapply exec_Icond; eauto.
    + apply Mem.unchanged_on_refl.
    + apply inject_separated_refl.
  - eexists. eexists. eexists. splits; eauto.
    + eapply exec_Ijumptable; eauto.
      generalize (REGSET1 r). rewrite H10. intro X. inv X. auto.
    + apply Mem.unchanged_on_refl.
    + apply inject_separated_refl.
Qed.
