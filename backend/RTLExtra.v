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
  f_equal. eauto using Int.add_zero_l.
Qed.

Lemma shift_stack_operation_Int_zero op:
  shift_stack_operation Int.zero op = op.
Proof.
  destruct op; auto. simpl. f_equal.
  eauto using Int.add_zero_l, shift_stack_addressing_Int_zero.
Qed.

(* copy *) Lemma inject_separated_refl F m tm:
(* copy *)   inject_separated F F m tm.
(* copy *) Proof. ii. congruence. Qed.

(* copy *) Definition regset_inject F rs trs :=
(* copy *)   forall r, val_inject F rs # r trs # r.

(* copy *) Definition regset_inject_incr F1 F2 rs trs
(* copy *)            (INCR: inject_incr F1 F2)
(* copy *)            (INJ: regset_inject F1 rs trs):
(* copy *)   regset_inject F2 rs trs.
(* copy *) Proof. ii. eapply val_inject_incr; eauto. Qed.

(* copy *) Lemma regset_inject_val_inject F rs trs r
(* copy *)       (INJ: regset_inject F rs trs):
(* copy *)   val_inject F rs # r trs # r.
(* copy *) Proof. auto. Qed.

(* copy *) Lemma regset_inject_val_list_inject F rs trs l
(* copy *)       (INJ: regset_inject F rs trs):
(* copy *)   val_list_inject F rs ## l trs ## l.
(* copy *) Proof. induction l; constructor; auto. Qed.

(* copy *) Lemma regset_inject_set_reg:
(* copy *)   forall F rs rs' r v v',
(* copy *)   regset_inject F rs rs' ->
(* copy *)   val_inject F v v' ->
(* copy *)   regset_inject F (rs#r <- v) (rs'#r <- v').
(* copy *) Proof.
(* copy *)   ii. rewrite ? Regmap.gsspec. destruct (peq r0 r); auto.
(* copy *) Qed.

(* copy *) Lemma regset_inject_init_regs F args args' params
(* copy *)       (ARGS: val_list_inject F args args'):
(* copy *)   regset_inject F (init_regs args params) (init_regs args' params).
(* copy *) Proof.
(* copy *)   revert args args' ARGS. induction params; simpl; ii.
(* copy *)   - rewrite ? Regmap.gi. auto.
(* copy *)   - inv ARGS.
(* copy *)     + rewrite ? Regmap.gi. auto.
(* copy *)     + apply regset_inject_set_reg; auto.
(* copy *) Qed.

(* copy *) Definition regset_lessdef rs trs :=
(* copy *)   forall r, Val.lessdef rs # r trs # r.

(* copy *) Lemma regset_lessdef_val_lessdef_list rs trs l
(* copy *)       (INJ: regset_lessdef rs trs):
(* copy *)   Val.lessdef_list rs ## l trs ## l.
(* copy *) Proof. induction l; constructor; auto. Qed.

(* copy *) Lemma regset_lessdef_set_reg:
(* copy *)   forall rs rs' r v v',
(* copy *)   regset_lessdef rs rs' ->
(* copy *)   Val.lessdef v v' ->
(* copy *)   regset_lessdef (rs#r <- v) (rs'#r <- v').
(* copy *) Proof.
(* copy *)   ii. rewrite ? Regmap.gsspec. destruct (peq r0 r); auto.
(* copy *) Qed.

(* copy *) Lemma regset_lessdef_init_regs args args' params
(* copy *)       (ARGS: Val.lessdef_list args args'):
(* copy *)   regset_lessdef (init_regs args params) (init_regs args' params).
(* copy *) Proof.
(* copy *)   revert args args' ARGS. induction params; simpl; ii.
(* copy *)   - rewrite ? Regmap.gi. auto.
(* copy *)   - inv ARGS.
(* copy *)     + rewrite ? Regmap.gi. auto.
(* copy *)     + apply regset_lessdef_set_reg; auto.
(* copy *) Qed.

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

(* copy *) Lemma is_normal_identical
(* copy *)       ge s f sp pc1 rs1 m1 pc2 rs2 m2 tr
(* copy *)       tge ts
(* copy *)       (SYMBOL: forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s)
(* copy *)       (VARINFO: forall b, Genv.find_var_info tge b = Genv.find_var_info ge b)
(* copy *)       (NORMAL1: is_normal (State s f sp pc1 rs1 m1))
(* copy *)       (STEP: step ge (State s f sp pc1 rs1 m1) tr (State s f sp pc2 rs2 m2)):
(* copy *)     <<TSTEP: step tge (State ts f sp pc1 rs1 m1) tr (State ts f sp pc2 rs2 m2)>>.
(* copy *) Proof.
(* copy *)   simpl in *. destruct (fn_code f) ! pc1 as [[]|] eqn:X; clarify; inv STEP; clarify.
(* copy *)   - apply exec_Inop; eauto.
(* copy *)   - eapply exec_Iop; eauto.
(* copy *)     erewrite eval_operation_preserved; eauto.
(* copy *)   - eapply exec_Iload; eauto;
(* copy *)     erewrite eval_addressing_preserved; eauto.
(* copy *)   - eapply exec_Istore; eauto;
(* copy *)     erewrite eval_addressing_preserved; eauto.
(* copy *)   - eapply exec_Ibuiltin; eauto.
(* copy *)     eapply external_call_symbols_preserved; eauto.
(* copy *)   - eapply exec_Icond; eauto.
(* copy *)   - eapply exec_Ijumptable; eauto.
(* copy *) Qed.

(* copy *) Lemma is_normal_extends
(* copy *)       ge s f sp pc1 rs1 m1 pc2 rs2 m2 tr
(* copy *)       tge ts trs1 tm1
(* copy *)       (SYMBOL: forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s)
(* copy *)       (VARINFO: forall b, Genv.find_var_info tge b = Genv.find_var_info ge b)
(* copy *)       (NORMAL1: is_normal (State s f sp pc1 rs1 m1))
(* copy *)       (STEP: step ge (State s f sp pc1 rs1 m1) tr (State s f sp pc2 rs2 m2))
(* copy *)       (REGSET1: regset_lessdef rs1 trs1)
(* copy *)       (MEM1: Mem.extends m1 tm1):
(* copy *)   exists trs2 tm2,
(* copy *)     <<TSTEP: step tge (State ts f sp pc1 trs1 tm1) tr (State ts f sp pc2 trs2 tm2)>> /\
(* copy *)     <<REGSET2: regset_lessdef rs2 trs2>> /\
(* copy *)     <<MEM2: Mem.extends m2 tm2>>.
(* copy *) Proof.
(* copy *)   simpl in *. destruct (fn_code f) ! pc1 as [[]|] eqn:X; clarify; inv STEP; clarify.
(* copy *)   - eexists. eexists. splits; eauto.
(* copy *)     apply exec_Inop; eauto.
(* copy *)   - exploit eval_operation_lessdef; try apply H10; eauto.
(* copy *)     { apply regset_lessdef_val_lessdef_list. eauto. }
(* copy *)     intro. des.
(* copy *)     eexists. eexists. splits; eauto.
(* copy *)     + eapply exec_Iop; eauto.
(* copy *)       erewrite eval_operation_preserved; eauto.
(* copy *)     + apply regset_lessdef_set_reg; auto.
(* copy *)   - exploit eval_addressing_lessdef; try apply H10; eauto.
(* copy *)     { apply regset_lessdef_val_lessdef_list. eauto. }
(* copy *)     intro. des.
(* copy *)     exploit Mem.loadv_extends; eauto.
(* copy *)     intro. des.
(* copy *)     eexists. eexists. splits; eauto.
(* copy *)     + eapply exec_Iload; eauto;
(* copy *)       erewrite eval_addressing_preserved; eauto.
(* copy *)     + apply regset_lessdef_set_reg; auto.
(* copy *)   - exploit eval_addressing_lessdef; try apply H10; eauto.
(* copy *)     { apply regset_lessdef_val_lessdef_list. eauto. }
(* copy *)     intro. des.
(* copy *)     exploit Mem.storev_extends; eauto.
(* copy *)     intro. des.
(* copy *)     eexists. eexists. splits; eauto.
(* copy *)     + eapply exec_Istore; eauto;
(* copy *)       erewrite eval_addressing_preserved; eauto.
(* copy *)   - exploit external_call_mem_extends; eauto.
(* copy *)     { apply regset_lessdef_val_lessdef_list. eauto. }
(* copy *)     intro. des. eexists. eexists. splits; try apply H1; eauto.
(* copy *)     + econs; eauto.
(* copy *)       eapply external_call_symbols_preserved; eauto. 
(* copy *)     + apply regset_lessdef_set_reg; auto.
(* copy *)   - exploit eval_condition_lessdef; try apply H10; eauto.
(* copy *)     { apply regset_lessdef_val_lessdef_list. eauto. }
(* copy *)     intro.
(* copy *)     eexists. eexists. splits; eauto.
(* copy *)     eapply exec_Icond; eauto.
(* copy *)   - eexists. eexists. splits; eauto.
(* copy *)     eapply exec_Ijumptable; eauto.
(* copy *)     generalize (REGSET1 r). rewrite H10. intro X. inv X. auto.
(* copy *) Qed.
