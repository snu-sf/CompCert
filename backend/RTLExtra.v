Require Import Coqlib.
Require Import Maps.
Require Import Integers.
Require Import Values.
Require Import AST.
Require Import Memory.
Require Import Globalenvs.
Require Import Events.
Require Import Op.
Require Import Registers.
Require Import RTL.
Require Import sflib.

Set Implicit Arguments.

Lemma shift_stack_addressing_Int_zero addr:
  shift_stack_addressing Int.zero addr = addr.
Proof.
  destruct addr; auto. simpl.
  f_equal. apply Int.add_zero_l.
Qed.

Lemma shift_stack_operation_Int_zero op:
  shift_stack_operation Int.zero op = op.
Proof.
  destruct op; auto. simpl. f_equal.
  apply shift_stack_addressing_Int_zero.
Qed.

Lemma inject_separated_refl F m tm:
  inject_separated F F m tm.
Proof. ii. congruence. Qed.

Definition regset_inject F rs trs :=
  forall r, val_inject F rs # r trs # r.

Definition regset_inject_incr F1 F2 rs trs
           (INCR: inject_incr F1 F2)
           (INJ: regset_inject F1 rs trs):
  regset_inject F2 rs trs.
Proof. ii. eapply val_inject_incr; eauto. Qed.

Lemma regset_inject_val_inject F rs trs r
      (INJ: regset_inject F rs trs):
  val_inject F rs # r trs # r.
Proof. auto. Qed.

Lemma regset_inject_val_list_inject F rs trs l
      (INJ: regset_inject F rs trs):
  val_list_inject F rs ## l trs ## l.
Proof. induction l; constructor; auto. Qed.

Lemma regset_inject_set_reg:
  forall F rs rs' r v v',
  regset_inject F rs rs' ->
  val_inject F v v' ->
  regset_inject F (rs#r <- v) (rs'#r <- v').
Proof.
  ii. rewrite ? Regmap.gsspec. destruct (peq r0 r); auto.
Qed.

Lemma regset_inject_init_regs F args args' params
      (ARGS: val_list_inject F args args'):
  regset_inject F (init_regs args params) (init_regs args' params).
Proof.
  revert args args' ARGS. induction params; simpl; ii.
  - rewrite ? Regmap.gi. auto.
  - inv ARGS.
    + rewrite ? Regmap.gi. auto.
    + apply regset_inject_set_reg; auto.
Qed.

Definition regset_lessdef rs trs :=
  forall r, Val.lessdef rs # r trs # r.

Lemma regset_lessdef_val_lessdef_list rs trs l
      (INJ: regset_lessdef rs trs):
  Val.lessdef_list rs ## l trs ## l.
Proof. induction l; constructor; auto. Qed.

Lemma regset_lessdef_set_reg:
  forall rs rs' r v v',
  regset_lessdef rs rs' ->
  Val.lessdef v v' ->
  regset_lessdef (rs#r <- v) (rs'#r <- v').
Proof.
  ii. rewrite ? Regmap.gsspec. destruct (peq r0 r); auto.
Qed.

Lemma regset_lessdef_init_regs args args' params
      (ARGS: Val.lessdef_list args args'):
  regset_lessdef (init_regs args params) (init_regs args' params).
Proof.
  revert args args' ARGS. induction params; simpl; ii.
  - rewrite ? Regmap.gi. auto.
  - inv ARGS.
    + rewrite ? Regmap.gi. auto.
    + apply regset_lessdef_set_reg; auto.
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

Lemma is_normal_identical
      ge s f sp pc1 rs1 m1 pc2 rs2 m2 tr
      tge ts
      (SYMBOL: forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s)
      (VARINFO: forall b, Genv.find_var_info tge b = Genv.find_var_info ge b)
      (NORMAL1: is_normal (State s f sp pc1 rs1 m1))
      (STEP: step ge (State s f sp pc1 rs1 m1) tr (State s f sp pc2 rs2 m2)):
    <<TSTEP: step tge (State ts f sp pc1 rs1 m1) tr (State ts f sp pc2 rs2 m2)>>.
Proof.
  simpl in *. destruct (fn_code f) ! pc1 as [[]|] eqn:X; clarify; inv STEP; clarify.
  - apply exec_Inop; eauto.
  - eapply exec_Iop; eauto.
    erewrite eval_operation_preserved; eauto.
  - eapply exec_Iload; eauto.
    erewrite eval_addressing_preserved; eauto.
  - eapply exec_Istore; eauto.
    erewrite eval_addressing_preserved; eauto.
  - eapply exec_Ibuiltin; eauto.
    eapply external_call_symbols_preserved; eauto.
  - eapply exec_Icond; eauto.
  - eapply exec_Ijumptable; eauto.
Qed.

Lemma is_normal_extends
      ge s f sp pc1 rs1 m1 pc2 rs2 m2 tr
      tge ts trs1 tm1
      (SYMBOL: forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s)
      (VARINFO: forall b, Genv.find_var_info tge b = Genv.find_var_info ge b)
      (NORMAL1: is_normal (State s f sp pc1 rs1 m1))
      (STEP: step ge (State s f sp pc1 rs1 m1) tr (State s f sp pc2 rs2 m2))
      (REGSET1: regset_lessdef rs1 trs1)
      (MEM1: Mem.extends m1 tm1):
  exists trs2 tm2,
    <<TSTEP: step tge (State ts f sp pc1 trs1 tm1) tr (State ts f sp pc2 trs2 tm2)>> /\
    <<REGSET2: regset_lessdef rs2 trs2>> /\
    <<MEM2: Mem.extends m2 tm2>>.
Proof.
  simpl in *. destruct (fn_code f) ! pc1 as [[]|] eqn:X; clarify; inv STEP; clarify.
  - eexists. eexists. splits; eauto.
    apply exec_Inop; eauto.
  - exploit eval_operation_lessdef; try apply H10; eauto.
    { apply regset_lessdef_val_lessdef_list. eauto. }
    intro. des.
    eexists. eexists. splits; eauto.
    + eapply exec_Iop; eauto.
      erewrite eval_operation_preserved; eauto.
    + apply regset_lessdef_set_reg; auto.
  - exploit eval_addressing_lessdef; try apply H10; eauto.
    { apply regset_lessdef_val_lessdef_list. eauto. }
    intro. des.
    exploit Mem.loadv_extends; eauto.
    intro. des.
    eexists. eexists. splits; eauto.
    + eapply exec_Iload; eauto.
      erewrite eval_addressing_preserved; eauto.
    + apply regset_lessdef_set_reg; auto.
  - exploit eval_addressing_lessdef; try apply H10; eauto.
    { apply regset_lessdef_val_lessdef_list. eauto. }
    intro. des.
    exploit Mem.storev_extends; eauto.
    intro. des.
    eexists. eexists. splits; eauto.
    + eapply exec_Istore; eauto.
      erewrite eval_addressing_preserved; eauto.
  - exploit external_call_mem_extends; eauto.
    { apply regset_lessdef_val_lessdef_list. eauto. }
    intro. des. eexists. eexists. splits; try apply H1; eauto.
    + econs; eauto.
      eapply external_call_symbols_preserved; eauto. 
    + apply regset_lessdef_set_reg; auto.
  - exploit eval_condition_lessdef; try apply H10; eauto.
    { apply regset_lessdef_val_lessdef_list. eauto. }
    intro.
    eexists. eexists. splits; eauto.
    eapply exec_Icond; eauto.
  - eexists. eexists. splits; eauto.
    eapply exec_Ijumptable; eauto.
    generalize (REGSET1 r). rewrite H10. intro X. inv X. auto.
Qed.
