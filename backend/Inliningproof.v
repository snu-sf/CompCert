(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** RTL function inlining: semantic preservation *)

Require Import Coqlib Wfsimpl Maps Errors Integers.
Require Import AST Linking Values Memory Globalenvs Stackenvs Events Smallstep.
Require Import Op Registers RTL.
Require Import Inlining Inliningspec.

Definition match_prog (prog tprog: program) :=
  match_program (fun cunit f tf => transf_fundef (funenv_program cunit) f = OK tf) eq prog tprog.

Lemma transf_program_match:
  forall prog tprog, transf_program prog = OK tprog -> match_prog prog tprog.
Proof.
  intros. eapply match_transform_partial_program_contextual; eauto.
Qed.

Section INLINING.

Variable prog: program.
Variable tprog: program.
Hypothesis TRANSF: match_prog prog tprog.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof (Genv.find_symbol_match TRANSF).

Lemma senv_preserved:
  Senv.equiv ge tge.
Proof (Genv.senv_match TRANSF).

Lemma functions_translated:
  forall (v: val) (f: fundef),
  Genv.find_funct ge v = Some f ->
  exists cu f', Genv.find_funct tge v = Some f' /\ transf_fundef (funenv_program cu) f = OK f' /\ linkorder cu prog.
Proof (Genv.find_funct_match TRANSF).

Lemma function_ptr_translated:
  forall (b: block) (f: fundef),
  Genv.find_funct_ptr ge b = Some f ->
  exists cu f', Genv.find_funct_ptr tge b = Some f' /\ transf_fundef (funenv_program cu) f = OK f' /\ linkorder cu prog.
Proof (Genv.find_funct_ptr_match TRANSF).

Lemma sig_function_translated:
  forall cu f f', transf_fundef (funenv_program cu) f = OK f' -> funsig f' = funsig f.
Proof.
  intros. destruct f; Errors.monadInv H; simpl; auto.
Qed.

(** ** Properties of contexts and relocations *)

Remark sreg_below_diff:
  forall ctx r r', Plt r' ctx.(dreg) -> sreg ctx r <> r'.
Proof.
  intros. zify. unfold sreg; rewrite shiftpos_eq. extlia.
Qed.

Remark context_reg_below_diff:
  forall ctx1 ctx2 r1 r2,
  context_reg_below ctx1 ctx2 -> Ple r1 ctx1.(mreg) -> sreg ctx1 r1 <> sreg ctx2 r2.
Proof.
  intros. red in H. zify. unfold sreg; rewrite ! shiftpos_eq. extlia.
Qed.

Remark context_reg_below_lt:
  forall ctx1 ctx2 r, context_reg_below ctx1 ctx2 -> Ple r ctx1.(mreg) -> Plt (sreg ctx1 r) ctx2.(dreg).
Proof.
  intros. red in H. unfold Plt; zify. unfold sreg; rewrite shiftpos_eq.
  extlia.
Qed.

(*
Remark context_below_le:
  forall ctx1 ctx2 r, context_below ctx1 ctx2 -> Ple r ctx1.(mreg) -> Ple (sreg ctx1 r) ctx2.(dreg).
Proof.
  intros. red in H. unfold Ple; zify. unfold sreg; rewrite shiftpos_eq.
  extlia.
Qed.
*)

(** ** Agreement between register sets before and after inlining. *)

Definition agree_regs (F: meminj) (ctx: context) (rs rs': regset) :=
  (forall r, Ple r ctx.(mreg) -> Val.inject F rs#r rs'#(sreg ctx r))
/\(forall r, Plt ctx.(mreg) r -> rs#r = Vundef).

Definition val_reg_charact (F: meminj) (ctx: context) (rs': regset) (v: val) (r: reg) :=
  (Plt ctx.(mreg) r /\ v = Vundef) \/ (Ple r ctx.(mreg) /\ Val.inject F v rs'#(sreg ctx r)).

Remark Plt_Ple_dec:
  forall p q, {Plt p q} + {Ple q p}.
Proof.
  intros. destruct (plt p q). left; auto. right; extlia.
Qed.

Lemma agree_val_reg_gen:
  forall F ctx rs rs' r, agree_regs F ctx rs rs' -> val_reg_charact F ctx rs' rs#r r.
Proof.
  intros. destruct H as [A B].
  destruct (Plt_Ple_dec (mreg ctx) r).
  left. rewrite B; auto.
  right. auto.
Qed.

Lemma agree_val_regs_gen:
  forall F ctx rs rs' rl,
  agree_regs F ctx rs rs' -> list_forall2 (val_reg_charact F ctx rs') rs##rl rl.
Proof.
  induction rl; intros; constructor; auto. apply agree_val_reg_gen; auto.
Qed.

Lemma agree_val_reg:
  forall F ctx rs rs' r, agree_regs F ctx rs rs' -> Val.inject F rs#r rs'#(sreg ctx r).
Proof.
  intros. exploit agree_val_reg_gen; eauto. instantiate (1 := r). intros [[A B] | [A B]].
  rewrite B; auto.
  auto.
Qed.

Lemma agree_val_regs:
  forall F ctx rs rs' rl, agree_regs F ctx rs rs' -> Val.inject_list F rs##rl rs'##(sregs ctx rl).
Proof.
  induction rl; intros; simpl. constructor. constructor; auto. apply agree_val_reg; auto.
Qed.

Lemma agree_set_reg:
  forall F ctx rs rs' r v v',
  agree_regs F ctx rs rs' ->
  Val.inject F v v' ->
  Ple r ctx.(mreg) ->
  agree_regs F ctx (rs#r <- v) (rs'#(sreg ctx r) <- v').
Proof.
  unfold agree_regs; intros. destruct H. split; intros.
  repeat rewrite Regmap.gsspec.
  destruct (peq r0 r). subst r0. rewrite peq_true. auto.
  rewrite peq_false. auto. apply shiftpos_diff; auto.
  rewrite Regmap.gso. auto. extlia.
Qed.

Lemma agree_set_reg_undef:
  forall F ctx rs rs' r v',
  agree_regs F ctx rs rs' ->
  agree_regs F ctx (rs#r <- Vundef) (rs'#(sreg ctx r) <- v').
Proof.
  unfold agree_regs; intros. destruct H. split; intros.
  repeat rewrite Regmap.gsspec.
  destruct (peq r0 r). subst r0. rewrite peq_true. auto.
  rewrite peq_false. auto. apply shiftpos_diff; auto.
  rewrite Regmap.gsspec. destruct (peq r0 r); auto.
Qed.

Lemma agree_set_reg_undef':
  forall F ctx rs rs' r,
  agree_regs F ctx rs rs' ->
  agree_regs F ctx (rs#r <- Vundef) rs'.
Proof.
  unfold agree_regs; intros. destruct H. split; intros.
  rewrite Regmap.gsspec.
  destruct (peq r0 r). subst r0. auto. auto.
  rewrite Regmap.gsspec. destruct (peq r0 r); auto.
Qed.

Lemma agree_regs_invariant:
  forall F ctx rs rs1 rs2,
  agree_regs F ctx rs rs1 ->
  (forall r, Ple ctx.(dreg) r -> Plt r (ctx.(dreg) + ctx.(mreg)) -> rs2#r = rs1#r) ->
  agree_regs F ctx rs rs2.
Proof.
  unfold agree_regs; intros. destruct H. split; intros.
  rewrite H0. auto.
  apply shiftpos_above.
  eapply Pos.lt_le_trans. apply shiftpos_below. extlia.
  apply H1; auto.
Qed.

Lemma agree_regs_incr:
  forall F ctx rs1 rs2 F',
  agree_regs F ctx rs1 rs2 ->
  inject_incr F F' ->
  agree_regs F' ctx rs1 rs2.
Proof.
  intros. destruct H. split; intros. eauto. auto.
Qed.

Remark agree_regs_init:
  forall F ctx rs, agree_regs F ctx (Regmap.init Vundef) rs.
Proof.
  intros; split; intros. rewrite Regmap.gi; auto. rewrite Regmap.gi; auto.
Qed.

Lemma agree_regs_init_regs:
  forall F ctx rl vl vl',
  Val.inject_list F vl vl' ->
  (forall r, In r rl -> Ple r ctx.(mreg)) ->
  agree_regs F ctx (init_regs vl rl) (init_regs vl' (sregs ctx rl)).
Proof.
  induction rl; simpl; intros.
  apply agree_regs_init.
  inv H. apply agree_regs_init.
  apply agree_set_reg; auto.
Qed.

(** ** Executing sequences of moves *)

Lemma tr_moves_init_regs:
  forall F stk f ste m ctx1 ctx2, context_reg_below ctx1 ctx2 ->
  forall rdsts rsrcs vl pc1 pc2 rs1,
  tr_moves f.(fn_code) pc1 (sregs ctx1 rsrcs) (sregs ctx2 rdsts) pc2 ->
  (forall r, In r rdsts -> Ple r ctx2.(mreg)) ->
  list_forall2 (val_reg_charact F ctx1 rs1) vl rsrcs ->
  exists rs2,
    star step tge (State stk f ste pc1 rs1 m)
               E0 (State stk f ste pc2 rs2 m)
  /\ agree_regs F ctx2 (init_regs vl rdsts) rs2
  /\ forall r, Plt r ctx2.(dreg) -> rs2#r = rs1#r.
Proof.
  induction rdsts; simpl; intros.
(* rdsts = nil *)
  inv H0. exists rs1; split. apply star_refl. split. apply agree_regs_init. auto.
(* rdsts = a :: rdsts *)
  inv H2. inv H0.
  exists rs1; split. apply star_refl. split. apply agree_regs_init. auto.
  simpl in H0. inv H0.
  exploit IHrdsts; eauto. intros [rs2 [A [B C]]].
  exists (rs2#(sreg ctx2 a) <- (rs2#(sreg ctx1 b1))).
  split. eapply star_right. eauto. eapply exec_Iop; eauto. traceEq.
  split. destruct H3 as [[P Q] | [P Q]].
  subst a1. eapply agree_set_reg_undef; eauto.
  eapply agree_set_reg; eauto. rewrite C; auto.  apply context_reg_below_lt; auto.
  intros. rewrite Regmap.gso. auto. apply not_eq_sym. eapply sreg_below_diff; eauto.
  destruct H2; discriminate.
Qed.

(** ** Memory invariants *)

(** A stack location is private if it is not the image of a valid
   location and we have full rights on it. *)

Definition loc_private (F: meminj) (m m': mem) (sp': block) (ofs: Z) : Prop :=
  Mem.perm m' sp' ofs Cur Freeable /\
  (forall b delta, F b = Some(sp', delta) -> ~Mem.perm m b (ofs - delta) Max Nonempty).

(** Likewise, for a range of locations. *)

Definition range_private (F: meminj) (m m': mem) (sp': block) (lo hi: Z) : Prop :=
  forall ofs, lo <= ofs < hi -> loc_private F m m' sp' ofs.

Lemma range_private_invariant:
  forall F m m' sp' lo hi F1 m1 m1',
  range_private F m m' sp' lo hi ->
  (forall b delta ofs,
      F1 b = Some(sp', delta) ->
      Mem.perm m1 b ofs Max Nonempty ->
      lo <= ofs + delta < hi ->
      F b = Some(sp', delta) /\ Mem.perm m b ofs Max Nonempty) ->
  (forall ofs, Mem.perm m' sp' ofs Cur Freeable -> Mem.perm m1' sp' ofs Cur Freeable) ->
  range_private F1 m1 m1' sp' lo hi.
Proof.
  intros; red; intros. exploit H; eauto. intros [A B]. split; auto.
  intros; red; intros. exploit H0; eauto. lia. intros [P Q].
  eelim B; eauto.
Qed.

Lemma range_private_perms:
  forall F m m' sp lo hi,
  range_private F m m' sp lo hi ->
  Mem.range_perm m' sp lo hi Cur Freeable.
Proof.
  intros; red; intros. eapply H; eauto.
Qed.

Lemma range_private_alloc_left:
  forall F m m' sp' base hi sz m1 sp F1,
  range_private F m m' sp' base hi ->
  Mem.alloc m 0 sz = (m1, sp) ->
  F1 sp = Some(sp', base) ->
  (forall b, b <> sp -> F1 b = F b) ->
  range_private F1 m1 m' sp' (base + Z.max sz 0) hi.
Proof.
  intros; red; intros.
  exploit (H ofs). generalize (Z.le_max_r sz 0). lia. intros [A B].
  split; auto. intros; red; intros.
  exploit Mem.perm_alloc_inv; eauto.
  destruct (eq_block b sp); intros.
  subst b. rewrite H1 in H4; inv H4.
  rewrite Zmax_spec in H3. destruct (zlt 0 sz); lia.
  rewrite H2 in H4; auto. eelim B; eauto.
Qed.

Lemma range_private_free_left:
  forall F m m' sp base sz hi b m1,
  range_private F m m' sp (base + Z.max sz 0) hi ->
  Mem.free m b 0 sz = Some m1 ->
  F b = Some(sp, base) ->
  Mem.inject F m m' ->
  range_private F m1 m' sp base hi.
Proof.
  intros; red; intros.
  destruct (zlt ofs (base + Z.max sz 0)) as [z|z].
  red; split.
  replace ofs with ((ofs - base) + base) by lia.
  eapply Mem.perm_inject; eauto.
  eapply Mem.free_range_perm; eauto.
  rewrite Zmax_spec in z. destruct (zlt 0 sz); lia.
  intros; red; intros. destruct (eq_block b b0).
  subst b0. rewrite H1 in H4; inv H4.
  eelim Mem.perm_free_2; eauto. rewrite Zmax_spec in z. destruct (zlt 0 sz); lia.
  exploit Mem.mi_no_overlap; eauto.
  apply Mem.perm_cur_max. apply Mem.perm_implies with Freeable; auto with mem.
  eapply Mem.free_range_perm. eauto.
  instantiate (1 := ofs - base). rewrite Zmax_spec in z. destruct (zlt 0 sz); lia.
  eapply Mem.perm_free_3; eauto.
  intros [A | A]. congruence. lia.

  exploit (H ofs). lia. intros [A B]. split. auto.
  intros; red; intros. eelim B; eauto. eapply Mem.perm_free_3; eauto.
Qed.

Lemma range_private_extcall:
  forall F F' m1 m2 m1' m2' sp base hi,
  range_private F m1 m1' sp base hi ->
  (forall b ofs p,
     Mem.valid_block m1 b -> Mem.perm m2 b ofs Max p -> Mem.perm m1 b ofs Max p) ->
  Mem.unchanged_on (loc_out_of_reach F m1) m1' m2' ->
  Mem.inject F m1 m1' ->
  inject_incr F F' ->
  inject_separated F F' m1 m1' ->
  Mem.valid_block m1' sp ->
  range_private F' m2 m2' sp base hi.
Proof.
  intros until hi; intros RP PERM UNCH INJ INCR SEP VB.
  red; intros. exploit RP; eauto. intros [A B].
  split. eapply Mem.perm_unchanged_on; eauto.
  intros. red in SEP. destruct (F b) as [[sp1 delta1] |] eqn:?.
  exploit INCR; eauto. intros EQ; rewrite H0 in EQ; inv EQ.
  red; intros; eelim B; eauto. eapply PERM; eauto.
  red. destruct (plt b (Mem.nextblock m1)); auto.
  exploit Mem.mi_freeblocks; eauto. congruence.
  exploit SEP; eauto. tauto.
Qed.

Definition perm_range (m: mem) (b: block) (ofs sz: Z) :=
  Mem.perm m b ofs Max Nonempty -> 0 <= ofs <= sz.

Definition meminj_stack_vars (F: meminj) (ctx: context) (ve1 ve2: Venv.t) :=
  Venv.meminj_varenv ve1 ve2 F (sid ctx) flat_maddr.

Lemma meminj_stack_vars_invariant:
  forall F ctx ve1 ve2 F',
  meminj_stack_vars F ctx ve1 ve2 ->
  inject_incr F F' ->
  meminj_stack_vars F' ctx ve1 ve2.
Proof.
  unfold meminj_stack_vars, Venv.meminj_varenv; intros.
  exploit H; eauto. apply H in H1.
  destruct H1 as [id2 [b2 [delta [A [B [C D]]]]]].
  intros. exists id2, b2, delta. eauto.
Qed.

(** ** Relating global environments *)

Inductive match_globalenvs (F: meminj) (bound: block): Prop :=
  | mk_match_globalenvs
      (DOMAIN: forall b, Plt b bound -> F b = Some(b, 0))
      (IMAGE: forall b1 b2 delta, F b1 = Some(b2, delta) -> Plt b2 bound -> b1 = b2)
      (SYMBOLS: forall id b, Genv.find_symbol ge id = Some b -> Plt b bound)
      (FUNCTIONS: forall b fd, Genv.find_funct_ptr ge b = Some fd -> Plt b bound)
      (VARINFOS: forall b gv, Genv.find_var_info ge b = Some gv -> Plt b bound).

Lemma find_function_agree:
  forall ros rs fd F ctx rs' bound,
  find_function ge ros rs = Some fd ->
  agree_regs F ctx rs rs' ->
  match_globalenvs F bound ->
  exists cu fd',
  find_function tge (sros ctx ros) rs' = Some fd' /\ transf_fundef (funenv_program cu) fd = OK fd' /\ linkorder cu prog.
Proof.
  intros. destruct ros as [r | id]; simpl in *.
- (* register *)
  assert (EQ: rs'#(sreg ctx r) = rs#r).
  { exploit Genv.find_funct_inv; eauto. intros [b EQ].
    assert (A: Val.inject F rs#r rs'#(sreg ctx r)). eapply agree_val_reg; eauto.
    rewrite EQ in A; inv A.
    inv H1. rewrite DOMAIN in H5. inv H5. auto.
    apply FUNCTIONS with fd.
    rewrite EQ in H; rewrite Genv.find_funct_find_funct_ptr in H. auto.
  }
  rewrite EQ. eapply functions_translated; eauto.
- (* symbol *)
  rewrite symbols_preserved. destruct (Genv.find_symbol ge id); try discriminate.
  eapply function_ptr_translated; eauto.
Qed.

Lemma find_inlined_function:
  forall fenv id rs fd f,
  fenv_compat prog fenv ->
  find_function ge (inr id) rs = Some fd ->
  fenv!id = Some f ->
  fd = Internal f.
Proof.
  intros.
  apply H in H1. apply Genv.find_def_symbol in H1. destruct H1 as (b & A & B).
  simpl in H0. unfold ge, fundef in H0. rewrite A in H0.
  rewrite <- Genv.find_funct_ptr_iff in B.
  congruence.
Qed.

(** Translation of builtin arguments. *)

Lemma tr_builtin_arg:
  forall F bound ctx rs rs' ve ve' m m',
  match_globalenvs F bound ->
  agree_regs F ctx rs rs' ->
  meminj_stack_vars F ctx ve ve' ->
  Mem.inject F m m' ->
  forall a v,
  eval_builtin_arg ge (fun r => rs#r) (Stenv.of_venv ve flat_mid flat_maddr) m a v ->
  exists v', eval_builtin_arg tge (fun r => rs'#r) (Stenv.of_venv ve' flat_mid flat_maddr) m' (sbuiltinarg ctx a) v'
          /\ Val.inject F v v'.
Proof.
  intros until m'; intros MG AG SP MI. induction 1; simpl.
- exists rs'#(sreg ctx x); split. constructor. eapply agree_val_reg; eauto.
- econstructor; eauto with barg.
- econstructor; eauto with barg.
- econstructor; eauto with barg.
- econstructor; eauto with barg.
- exploit Mem.loadv_inject; eauto.
  instantiate (1 := Stenv.var_address (Stenv.of_venv ve' flat_mid flat_maddr) (sid ctx id) ofs).
    unfold Stenv.var_address, Stenv.move_addr, flat_mid, flat_maddr in *; simpl in *.
    destruct (Venv.find_var ve id) as [b1|] eqn:FS; auto.
    exploit SP. eauto. intros. destruct H0 as [id2 [b2 [delta [A [B [C D]]]]]].
    rewrite C, A. econstructor. eapply B. unfold flat_maddr in D; rewrite <- D.
    rewrite Ptrofs.add_zero; auto.
  intros (v' & A & B).
  exists v'; eauto with barg.
- econstructor; split. constructor.
  unfold Stenv.var_address, Stenv.move_addr, flat_mid, flat_maddr in *; simpl in *.
  destruct (Venv.find_var ve id) as [b1|] eqn:FS; auto.
  exploit SP. eauto. intros. destruct H as [id2 [b2 [delta [A [B [C D]]]]]].
  rewrite C, A. econstructor. eapply B. unfold flat_maddr in D; rewrite <- D.
  rewrite Ptrofs.add_zero; auto.
- assert (Val.inject F (Senv.symbol_address ge id ofs) (Senv.symbol_address tge id ofs)).
  { unfold Senv.symbol_address; simpl; unfold Genv.symbol_address.
    rewrite symbols_preserved. destruct (Genv.find_symbol ge id) as [b|] eqn:FS; auto.
    inv MG. econstructor. eauto. rewrite Ptrofs.add_zero; auto. }
  exploit Mem.loadv_inject; eauto. intros (v' & A & B).
  exists v'; eauto with barg.
- econstructor; split. constructor.
  unfold Senv.symbol_address; simpl; unfold Genv.symbol_address.
  rewrite symbols_preserved. destruct (Genv.find_symbol ge id) as [b|] eqn:FS; auto.
  inv MG. econstructor. eauto. rewrite Ptrofs.add_zero; auto.
- destruct IHeval_builtin_arg1 as (v1' & A1 & B1).
  destruct IHeval_builtin_arg2 as (v2' & A2 & B2).
  econstructor; split. eauto with barg. apply Val.longofwords_inject; auto.
- destruct IHeval_builtin_arg1 as (v1' & A1 & B1).
  destruct IHeval_builtin_arg2 as (v2' & A2 & B2).
  econstructor; split. eauto with barg.
  destruct Archi.ptr64; auto using Val.add_inject, Val.addl_inject.
Qed.

Lemma tr_builtin_args:
  forall F bound ctx rs rs' ve ve' m m',
  match_globalenvs F bound ->
  agree_regs F ctx rs rs' ->
  meminj_stack_vars F ctx ve ve' ->
  Mem.inject F m m' ->
  forall al vl,
  eval_builtin_args ge (fun r => rs#r) (Stenv.of_venv ve flat_mid flat_maddr) m al vl ->
  exists vl', eval_builtin_args tge (fun r => rs'#r) (Stenv.of_venv ve' flat_mid flat_maddr) m' (map (sbuiltinarg ctx) al) vl'
          /\ Val.inject_list F vl vl'.
Proof.
  induction 5; simpl.
- exists (@nil val); split; constructor.
- exploit tr_builtin_arg; eauto. intros (v1' & A & B).
  destruct IHlist_forall2 as (vl' & C & D).
  exists (v1' :: vl'); split; constructor; auto.
Qed.

(** ** Relating stacks *)

Inductive match_stacks (F: meminj) (m m': mem):
             list stackframe -> list stackframe -> block -> Prop :=
  | match_stacks_nil: forall bound1 bound
        (MG: match_globalenvs F bound1)
        (BELOW: Ple bound1 bound),
      match_stacks F m m' nil nil bound
  | match_stacks_cons: forall res f ve pc rs stk f' ve' rs' stk' bound fenv ctx
        (MS: match_stacks_inside F m m' stk stk' f' ctx ve' rs')
        (COMPAT: fenv_compat prog fenv)
        (FB: tr_funbody fenv ctx f f'.(fn_code))
        (AG: agree_regs F ctx rs rs')
        (SP: meminj_stack_vars F ctx ve ve')
        (RES: Ple res ctx.(mreg))
        (BELOW: Ple (Venv.nextblock ve') bound),
      match_stacks F m m'
                   (Stackframe res f (Stenv.of_venv ve flat_mid flat_maddr) pc rs :: stk)
                   (Stackframe (sreg ctx res) f' (Stenv.of_venv ve' flat_mid flat_maddr) (spc ctx pc) rs' :: stk')
                   bound
  | match_stacks_untailcall: forall stk res f' ve' rpc rs' stk' bound ctx
        (MS: match_stacks_inside F m m' stk stk' f' ctx ve' rs')
        (RET: ctx.(retinfo) = Some (rpc, res))
        (BELOW: Ple (Venv.nextblock ve') bound),
      match_stacks F m m'
                   stk
                   (Stackframe res f' (Stenv.of_venv ve' flat_mid flat_maddr) rpc rs' :: stk')
                   bound

with match_stacks_inside (F: meminj) (m m': mem):
        list stackframe -> list stackframe -> function -> context -> Venv.t -> regset -> Prop :=
  | match_stacks_inside_base: forall stk stk' f' ctx ve' rs'
        (MS: match_stacks F m m' stk stk' (Venv.baseblock ve'))
        (RET: ctx.(retinfo) = None)
        (DSTK: ctx.(dstk) = 1%positive),
      match_stacks_inside F m m' stk stk' f' ctx ve' rs'
  | match_stacks_inside_inlined: forall res f ve pc rs stk stk' f' fenv ctx ve' rs' ctx'
        (MS: match_stacks_inside F m m' stk stk' f' ctx' ve' rs')
        (COMPAT: fenv_compat prog fenv)
        (FB: tr_funbody fenv ctx' f f'.(fn_code))
        (AG: agree_regs F ctx' rs rs')
        (SP: meminj_stack_vars F ctx' ve ve')
        (RES: Ple res ctx'.(mreg))
        (RET: ctx.(retinfo) = Some (spc ctx' pc, sreg ctx' res))
        (BELOW: context_reg_below ctx' ctx)
        (SBELOW: context_stack_call_below ctx' ctx),
      match_stacks_inside F m m' (Stackframe res f (Stenv.of_venv ve flat_mid flat_maddr) pc rs :: stk)
                                 stk' f' ctx ve' rs'.

(** Properties of match_stacks *)

Section MATCH_STACKS.

Variable F: meminj.
Variables m m': mem.

Lemma match_stacks_globalenvs:
  forall stk stk' bound,
  match_stacks F m m' stk stk' bound -> exists b, match_globalenvs F b
with match_stacks_inside_globalenvs:
  forall stk stk' f ctx ve' rs',
  match_stacks_inside F m m' stk stk' f ctx ve' rs' -> exists b, match_globalenvs F b.
Proof.
  induction 1; eauto.
  induction 1; eauto.
Qed.

Lemma match_globalenvs_preserves_globals:
  forall b, match_globalenvs F b -> meminj_preserves_globals ge F.
Proof.
  intros. inv H. red. split. eauto. split. eauto.
  intros. symmetry. eapply IMAGE; eauto.
Qed.

Lemma match_stacks_inside_globals:
  forall stk stk' f ctx ve' rs',
  match_stacks_inside F m m' stk stk' f ctx ve' rs' -> meminj_preserves_globals ge F.
Proof.
  intros. exploit match_stacks_inside_globalenvs; eauto. intros [b A].
  eapply match_globalenvs_preserves_globals; eauto.
Qed.

Lemma match_stacks_bound:
  forall stk stk' bound bound1,
  match_stacks F m m' stk stk' bound ->
  Ple bound bound1 ->
  match_stacks F m m' stk stk' bound1.
Proof.
  intros. inv H.
  apply match_stacks_nil with bound0. auto. eapply Ple_trans; eauto.
  eapply match_stacks_cons; eauto. extlia.
  eapply match_stacks_untailcall; eauto. extlia.
Qed.

Variable F1: meminj.
Variables m1 m1': mem.
Hypothesis INCR: inject_incr F F1.

Lemma match_stacks_invariant:
  forall stk stk' bound, match_stacks F m m' stk stk' bound ->
  forall (INJ: forall b1 b2 delta,
               F1 b1 = Some(b2, delta) -> Plt b2 bound -> F b1 = Some(b2, delta))
         (PERM1: forall b1 b2 delta ofs,
               F1 b1 = Some(b2, delta) -> Plt b2 bound ->
               Mem.perm m1 b1 ofs Max Nonempty -> Mem.perm m b1 ofs Max Nonempty)
         (PERM2: forall b ofs, Plt b bound ->
               Mem.perm m' b ofs Cur Freeable -> Mem.perm m1' b ofs Cur Freeable)
         (PERM3: forall b ofs k p, Plt b bound ->
               Mem.perm m1' b ofs k p -> Mem.perm m' b ofs k p),
  match_stacks F1 m1 m1' stk stk' bound

with match_stacks_inside_invariant:
  forall stk stk' f' ctx ve' rs1,
  match_stacks_inside F m m' stk stk' f' ctx ve' rs1 ->
  forall rs2
         (RS: forall r, Plt r ctx.(dreg) -> rs2#r = rs1#r)
         (INJ: forall b1 b2 delta,
               F1 b1 = Some(b2, delta) -> Plt b2 (Venv.nextblock ve') -> F b1 = Some(b2, delta))
         (PERM1: forall b1 b2 delta ofs,
               F1 b1 = Some(b2, delta) -> Plt b2 (Venv.nextblock ve') ->
               Mem.perm m1 b1 ofs Max Nonempty -> Mem.perm m b1 ofs Max Nonempty)
         (PERM2: forall b ofs, Plt b (Venv.nextblock ve') ->
               Mem.perm m' b ofs Cur Freeable -> Mem.perm m1' b ofs Cur Freeable)
         (PERM3: forall b ofs k p, Plt b (Venv.nextblock ve') ->
               Mem.perm m1' b ofs k p -> Mem.perm m' b ofs k p),
  match_stacks_inside F1 m1 m1' stk stk' f' ctx ve' rs2.

Proof.
  induction 1; intros.
  (* nil *)
  apply match_stacks_nil with (bound1 := bound1).
  inv MG. constructor; auto.
  intros. apply IMAGE with delta. eapply INJ; eauto. eapply Pos.lt_le_trans; eauto.
  auto. auto.
  (* cons *)
  apply match_stacks_cons with (fenv := fenv) (ctx := ctx); auto.
  eapply match_stacks_inside_invariant; eauto.
  intros; eapply INJ; eauto. extlia.
  intros; eapply PERM1; eauto; extlia.
  intros; eapply PERM2; eauto; extlia.
  intros; eapply PERM3; eauto; extlia.
  eapply agree_regs_incr; eauto; extlia.
  eapply meminj_stack_vars_invariant; eauto.

  (* untailcall *)
  apply match_stacks_untailcall with (ctx := ctx); auto.
  eapply match_stacks_inside_invariant; eauto.
  intros; eapply INJ; eauto; extlia.
  intros; eapply PERM1; eauto; extlia.
  intros; eapply PERM2; eauto; extlia.
  intros; eapply PERM3; eauto; extlia.

  induction 1; intros.
  (* base *)
  eapply match_stacks_inside_base; eauto.
  eapply match_stacks_invariant; eauto.
  intros; eapply INJ; eauto; pose proof (Venv.checkpoint_order ve'); extlia.
  intros; eapply PERM1; eauto; pose proof (Venv.checkpoint_order ve'); extlia.
  intros; eapply PERM2; eauto; pose proof (Venv.checkpoint_order ve'); extlia.
  intros; eapply PERM3; eauto; pose proof (Venv.checkpoint_order ve'); extlia.
  (* inlined *)
  apply match_stacks_inside_inlined with (fenv := fenv) (ctx' := ctx'); auto.
  apply IHmatch_stacks_inside; auto.
  intros. apply RS. red in BELOW. extlia.
  apply agree_regs_incr with F; auto.
  apply agree_regs_invariant with rs'; auto.
  intros. apply RS. red in BELOW. extlia.
  eapply meminj_stack_vars_invariant; eauto.
Qed.

Lemma match_stacks_empty:
  forall stk stk' bound,
  match_stacks F m m' stk stk' bound -> stk = nil -> stk' = nil
with match_stacks_inside_empty:
  forall stk stk' f ctx ve rs,
  match_stacks_inside F m m' stk stk' f ctx ve rs -> stk = nil -> stk' = nil /\ ctx.(retinfo) = None.
Proof.
  induction 1; intros.
  auto.
  discriminate.
  exploit match_stacks_inside_empty; eauto. intros [A B]. congruence.
  induction 1; intros.
  split. eapply match_stacks_empty; eauto. auto.
  discriminate.
Qed.

End MATCH_STACKS.

(** Preservation by assignment to a register *)

Lemma match_stacks_inside_set_reg:
  forall F m m' stk stk' f' ctx ve' rs' r v,
  match_stacks_inside F m m' stk stk' f' ctx ve' rs' ->
  match_stacks_inside F m m' stk stk' f' ctx ve' (rs'#(sreg ctx r) <- v).
Proof.
  intros. eapply match_stacks_inside_invariant; eauto.
  intros. apply Regmap.gso. zify. unfold sreg; rewrite shiftpos_eq. extlia.
Qed.

Lemma match_stacks_inside_set_res:
  forall F m m' stk stk' f' ctx ve' rs' res v,
  match_stacks_inside F m m' stk stk' f' ctx ve' rs' ->
  match_stacks_inside F m m' stk stk' f' ctx ve' (regmap_setres (sbuiltinres ctx res) v rs').
Proof.
  intros. destruct res; simpl; auto.
  apply match_stacks_inside_set_reg; auto.
Qed.

(** Preservation by a memory store *)

Lemma match_stacks_inside_store:
  forall F m m' stk stk' f' ctx ve' rs' chunk b ofs v m1 chunk' b' ofs' v' m1',
  match_stacks_inside F m m' stk stk' f' ctx ve' rs' ->
  Mem.store chunk m b ofs v = Some m1 ->
  Mem.store chunk' m' b' ofs' v' = Some m1' ->
  match_stacks_inside F m1 m1' stk stk' f' ctx ve' rs'.
Proof.
  intros.
  eapply match_stacks_inside_invariant; eauto with mem.
Qed.

(** Preservation by an allocation *)

Lemma match_stacks_inside_alloc_left:
  forall F m m' stk stk' f' ctx ve' rs',
  match_stacks_inside F m m' stk stk' f' ctx ve' rs' ->
  forall id sz m1 b b' F1,
  Mem.alloc m 0 sz = (m1, b) ->
  inject_incr F F1 ->
  Venv.find_var ve' id = Some b' ->
  F1 b = Some(b', 0) ->
  (forall b1, b1 <> b -> F1 b1 = F b1) ->
  Ple ctx.(dstk) id ->
  match_stacks_inside F1 m1 m' stk stk' f' ctx ve' rs'.
Proof.
  induction 1; intros.
  (* base *)
  eapply match_stacks_inside_base; eauto.
  eapply match_stacks_invariant; eauto.
  intros. destruct (eq_block b1 b).
  subst b1. rewrite H2 in H5; inv H5.
  apply (Venv.range ve' id) in H1. inv H1.
  apply Plt_Ple_trans with (r := b2) in H6. eelim Plt_strict; eauto. apply Plt_Ple; auto.
  rewrite H3 in H5; auto.
  intros. exploit Mem.perm_alloc_inv; eauto. destruct (eq_block b1 b); intros; auto.
  subst b1. rewrite H2 in H5. inv H5.
  apply (Venv.range ve' id) in H1. inv H1.
  apply Plt_Ple_trans with (r := b2) in H6. eelim Plt_strict; eauto. apply Plt_Ple; auto.
  (* inlined *)
  eapply match_stacks_inside_inlined; eauto.
  eapply IHmatch_stacks_inside; eauto.
  unfold context_stack_call_below, shiftpos in SBELOW; extlia.
  eapply agree_regs_incr; eauto.
  eapply meminj_stack_vars_invariant; eauto.
Qed.

(** Preservation by freeing *)

Lemma match_stacks_free_left:
  forall F m m' stk stk' ve b lo hi m1,
  match_stacks F m m' stk stk' (Venv.nextblock ve) ->
  Mem.free m b lo hi = Some m1 ->
  match_stacks F m1 m' stk stk' (Venv.nextblock ve).
Proof.
  intros. eapply match_stacks_invariant; eauto.
  intros. eapply Mem.perm_free_3; eauto.
Qed.

(* Lemma match_stacks_free_right: *)
(*   forall F m m' stk stk' ve lo hi m1', *)
(*   match_stacks F m m' stk stk' (Venv.ceil ve) -> *)
(*   Mem.free m' lo hi = Some m1' -> *)
(*   match_stacks F m m1' stk stk' (Venv.ceil ve). *)
(* Proof. *)
(*   intros. eapply match_stacks_invariant; eauto. *)
(*   intros. eapply Mem.perm_free_1; eauto with ordered_type. *)
(*   intros. eapply Mem.perm_free_3; eauto. *)
(* Qed. *)

Lemma min_alignment_sound:
  forall sz n, (min_alignment sz | n) -> Mem.inj_offset_aligned n sz.
Proof.
  intros; red; intros. unfold min_alignment in H.
  assert (2 <= sz -> (2 | n)). intros.
    destruct (zle sz 1). extlia.
    destruct (zle sz 2). auto.
    destruct (zle sz 4). apply Z.divide_trans with 4; auto. exists 2; auto.
    apply Z.divide_trans with 8; auto. exists 4; auto.
  assert (4 <= sz -> (4 | n)). intros.
    destruct (zle sz 1). extlia.
    destruct (zle sz 2). extlia.
    destruct (zle sz 4). auto.
    apply Z.divide_trans with 8; auto. exists 2; auto.
  assert (8 <= sz -> (8 | n)). intros.
    destruct (zle sz 1). extlia.
    destruct (zle sz 2). extlia.
    destruct (zle sz 4). extlia.
    auto.
  destruct chunk; simpl in *; auto.
  apply Z.divide_1_l.
  apply Z.divide_1_l.
  apply H2; lia.
  apply H2; lia.
Qed.

(** Preservation by external calls *)

Section EXTCALL.

Variables F1 F2: meminj.
Variables m1 m2 m1' m2': mem.
Hypothesis MAXPERM: forall b ofs p, Mem.valid_block m1 b -> Mem.perm m2 b ofs Max p -> Mem.perm m1 b ofs Max p.
Hypothesis MAXPERM': forall b ofs p, Mem.valid_block m1' b -> Mem.perm m2' b ofs Max p -> Mem.perm m1' b ofs Max p.
Hypothesis UNCHANGED: Mem.unchanged_on (loc_out_of_reach F1 m1) m1' m2'.
Hypothesis INJ: Mem.inject F1 m1 m1'.
Hypothesis INCR: inject_incr F1 F2.
Hypothesis SEP: inject_separated F1 F2 m1 m1'.

Lemma match_stacks_extcall:
  forall stk stk' bound,
  match_stacks F1 m1 m1' stk stk' bound ->
  Ple bound (Mem.nextblock m1') ->
  match_stacks F2 m2 m2' stk stk' bound
with match_stacks_inside_extcall:
  forall stk stk' f' ctx ve' rs',
  match_stacks_inside F1 m1 m1' stk stk' f' ctx ve' rs' ->
  Ple (Venv.nextblock ve') (Mem.nextblock m1') ->
  match_stacks_inside F2 m2 m2' stk stk' f' ctx ve' rs'.
Proof.
  induction 1; intros.
  apply match_stacks_nil with bound1; auto.
    inv MG. constructor; intros; eauto.
    destruct (F1 b1) as [[b2' delta']|] eqn:?.
    exploit INCR; eauto. intros EQ; rewrite H0 in EQ; inv EQ. eapply IMAGE; eauto.
    exploit SEP; eauto. intros [A B]. elim B. red. extlia.
  eapply match_stacks_cons; eauto.
    eapply match_stacks_inside_extcall; eauto. extlia.
    eapply agree_regs_incr; eauto.
    unfold meminj_stack_vars.
    eapply meminj_stack_vars_invariant; eauto.

  eapply match_stacks_untailcall; eauto.
  eapply match_stacks_inside_extcall; eauto. extlia.
  induction 1; intros.
  eapply match_stacks_inside_base; eauto.
  eapply match_stacks_extcall; eauto.
    pose proof (Venv.checkpoint_order ve'). extlia.
  eapply match_stacks_inside_inlined; eauto.
    eapply agree_regs_incr; eauto.
    eapply meminj_stack_vars_invariant; eauto.
Qed.

End EXTCALL.

(** Change of context corresponding to an inlined tailcall *)

Lemma align_unchanged:
  forall n amount, amount > 0 -> (amount | n) -> align n amount = n.
Proof.
  intros. destruct H0 as [p EQ]. subst n. unfold align. decEq.
  apply Zdiv_unique with (b := amount - 1). lia. lia.
Qed.

Lemma match_stacks_inside_inlined_tailcall:
  forall fenv F m m' stk stk' f' ctx ve' rs' ctx' f,
  match_stacks_inside F m m' stk stk' f' ctx ve' rs' ->
  context_reg_below ctx ctx' ->
  context_stack_tailcall_below ctx ctx' ->
  ctx'.(retinfo) = ctx.(retinfo) ->
  tr_funbody fenv ctx' f f'.(fn_code) ->
  match_stacks_inside F m m' stk stk' f' ctx' ve' rs'.
Proof.
  intros. inv H.
  (* base *)
  eapply match_stacks_inside_base; eauto. congruence.
  rewrite H1. rewrite DSTK. auto.
  (* inlined *)
  assert (forall id, sid ctx id = sid ctx' id). intros. unfold sid. inv H1. auto.
  eapply match_stacks_inside_inlined; eauto.
  congruence.
  unfold context_reg_below in *. extlia.
  unfold context_stack_call_below in *. rewrite <- SBELOW; apply H1.
Qed.

(** ** Relating states *)

Inductive match_states: RTL.state -> RTL.state -> Prop :=
  | match_regular_states: forall stk f ve pc rs m stk' f' ve' rs' m' F fenv ctx
        (MS: match_stacks_inside F m m' stk stk' f' ctx ve' rs')
        (COMPAT: fenv_compat prog fenv)
        (FB: tr_funbody fenv ctx f f'.(fn_code))
        (AG: agree_regs F ctx rs rs')
        (SP: meminj_stack_vars F ctx ve ve')
        (MINJ: Mem.inject F m m')
        (VB: forall b, Venv.valid_block ve' b -> Mem.valid_block m' b),
      match_states (State stk f (Stenv.of_venv ve flat_mid flat_maddr) pc rs m)
                   (State stk' f' (Stenv.of_venv ve' flat_mid flat_maddr) (spc ctx pc) rs' m')
  | match_call_states: forall stk fd args m stk' fd' args' m' cunit F
        (MS: match_stacks F m m' stk stk' (Mem.nextblock m'))
        (LINK: linkorder cunit prog)
        (FD: transf_fundef (funenv_program cunit) fd = OK fd')
        (VINJ: Val.inject_list F args args')
        (MINJ: Mem.inject F m m'),
      match_states (Callstate stk fd args m)
                   (Callstate stk' fd' args' m')
  | match_call_regular_states: forall stk f vargs m stk' f' ve' rs' m' F fenv ctx ctx' pc' pc1' rargs
        (MS: match_stacks_inside F m m' stk stk' f' ctx ve' rs')
        (COMPAT: fenv_compat prog fenv)
        (FB: tr_funbody fenv ctx f f'.(fn_code))
        (BELOW: context_reg_below ctx' ctx)
        (NOP: f'.(fn_code)!pc' = Some(Inop pc1'))
        (MOVES: tr_moves f'.(fn_code) pc1' (sregs ctx' rargs) (sregs ctx f.(fn_params)) (spc ctx f.(fn_entrypoint)))
        (VINJ: list_forall2 (val_reg_charact F ctx' rs') vargs rargs)
        (MINJ: Mem.inject F m m')
        (VB: forall b, Venv.valid_block ve' b -> Mem.valid_block m' b),
      match_states (Callstate stk (Internal f) vargs m)
                   (State stk' f' (Stenv.of_venv ve' flat_mid flat_maddr) pc' rs' m')
  | match_return_states: forall stk v m stk' v' m' F
        (MS: match_stacks F m m' stk stk' (Mem.nextblock m'))
        (VINJ: Val.inject F v v')
        (MINJ: Mem.inject F m m'),
      match_states (Returnstate stk v m)
                   (Returnstate stk' v' m')
  | match_return_regular_states: forall stk v m stk' f' ve' rs' m' F ctx pc' or rinfo
        (MS: match_stacks_inside F m m' stk stk' f' ctx ve' rs')
        (RET: ctx.(retinfo) = Some rinfo)
        (AT: f'.(fn_code)!pc' = Some(inline_return ctx or rinfo))
        (VINJ: match or with None => v = Vundef | Some r => Val.inject F v rs'#(sreg ctx r) end)
        (MINJ: Mem.inject F m m')
        (VB: forall b, Venv.valid_block ve' b -> Mem.valid_block m' b),
      match_states (Returnstate stk v m)
                   (State stk' f' (Stenv.of_venv ve' flat_mid flat_maddr) pc' rs' m').

(** ** Forward simulation *)

Definition measure (S: RTL.state) : nat :=
  match S with
  | State _ _ _ _ _ _ => 1%nat
  | Callstate _ _ _ _ => 0%nat
  | Returnstate _ _ _ => 0%nat
  end.

Lemma tr_funbody_inv:
  forall fenv cts f c pc i,
  tr_funbody fenv cts f c -> f.(fn_code)!pc = Some i -> tr_instr fenv cts pc i c.
Proof.
  intros. inv H. eauto.
Qed.

Theorem step_simulation:
  forall S1 t S2,
  step ge S1 t S2 ->
  forall S1' (MS: match_states S1 S1'),
  (exists S2', plus step tge S1' t S2' /\ match_states S2 S2')
  \/ (measure S2 < measure S1 /\ t = E0 /\ match_states S2 S1')%nat.
Proof.
  induction 1; intros; inv MS.

- (* nop *)
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
  left; econstructor; split.
  eapply plus_one. eapply exec_Inop; eauto.
  econstructor; eauto.

- (* op *)
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
  exploit eval_operation_inject.
    eapply match_stacks_inside_globals; eauto.
    eexact SP.
    instantiate (2 := rs##args). instantiate (1 := rs'##(sregs ctx args)). eapply agree_val_regs; eauto.
    eexact MINJ. eauto.
  fold (sop ctx op). intros [v' [A B]].
  left; econstructor; split.
  eapply plus_one. eapply exec_Iop; eauto. erewrite eval_operation_preserved; eauto.
  exact symbols_preserved.
  econstructor; eauto.
  apply match_stacks_inside_set_reg; auto.
  apply agree_set_reg; auto.

- (* load *)
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
  exploit eval_addressing_inject.
    eapply match_stacks_inside_globals; eauto.
    eexact SP.
    instantiate (2 := rs##args). instantiate (1 := rs'##(sregs ctx args)). eapply agree_val_regs; eauto.
    eauto.
  fold (saddr ctx addr). intros [a' [P Q]].
  exploit Mem.loadv_inject; eauto. intros [v' [U V]].
  assert (eval_addressing tge (Stenv.of_venv ve' flat_mid flat_maddr) (saddr ctx addr) rs' ## (sregs ctx args) = Some a').
  rewrite <- P. apply eval_addressing_preserved. exact symbols_preserved.
  left; econstructor; split.
  eapply plus_one. eapply exec_Iload; eauto.
  econstructor; eauto.
  apply match_stacks_inside_set_reg; auto.
  apply agree_set_reg; auto.

- (* store *)
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
  exploit eval_addressing_inject.
    eapply match_stacks_inside_globals; eauto.
    eexact SP.
    instantiate (2 := rs##args). instantiate (1 := rs'##(sregs ctx args)). eapply agree_val_regs; eauto.
    eauto.
  fold saddr. intros [a' [P Q]].
  exploit Mem.storev_mapped_inject; eauto. eapply agree_val_reg; eauto.
  intros [m1' [U V]].
  assert (eval_addressing tge (Stenv.of_venv ve' flat_mid flat_maddr) (saddr ctx addr) rs' ## (sregs ctx args) = Some a').
    rewrite <- P. apply eval_addressing_preserved. exact symbols_preserved.
  left; econstructor; split.
  eapply plus_one. eapply exec_Istore; eauto.
  destruct a; simpl in H1; try discriminate.
  destruct a'; simpl in U; try discriminate.
  econstructor; eauto.
  eapply match_stacks_inside_store; eauto.
  intros. apply VB in H3.
  eapply Mem.store_valid_block_1; eauto.

- (* call *)
  exploit match_stacks_inside_globalenvs; eauto. intros [bound G].
  exploit find_function_agree; eauto. intros (cu & fd' & A & B & C).
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
+ (* not inlined *)
  left; econstructor; split.
  eapply plus_one. eapply exec_Icall; eauto.
  eapply sig_function_translated; eauto.
  econstructor; eauto.
  eapply match_stacks_cons; eauto.
    pose proof (Venv.lastblock_valid ve') as LV.
    apply VB in LV. unfold Mem.valid_block in LV.
    pose proof (Venv.succ_nextblock_lastblock ve'). extlia.
  eapply agree_val_regs; eauto.
+ (* inlined *)
  assert (EQ: fd = Internal f0) by (eapply find_inlined_function; eauto).
  subst fd.
  right; split. simpl; lia. split. auto.
  econstructor; eauto.
  eapply match_stacks_inside_inlined; eauto.
  apply agree_val_regs_gen; auto.

- (* tailcall *)
  exploit match_stacks_inside_globalenvs; eauto. intros [bound G].
  exploit find_function_agree; eauto. intros (cu & fd' & A & B & C).
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
+ (* within the original function *)
  inv MS0; try congruence.
  assert (X: { m1' | Mem.free_list m'0 (Venv.blocks_of_venv ve' (fn_stackspaces f')) = Some m1'}). admit.
  destruct X as [m1' FREE].
  left; econstructor; split.
  eapply plus_one. eapply exec_Itailcall; eauto.
  eapply sig_function_translated; eauto.
  econstructor; eauto.
  eapply match_stacks_bound with (bound := Venv.baseblock ve').
  eapply match_stacks_invariant; eauto.
    intros. eapply Mem.perm_free_list; eauto.
    admit.
    intros. eapply Mem.perm_free_list; eauto.
  admit.
  eapply agree_val_regs; eauto.
  eapply Mem.free_right_inject; eauto. eapply Mem.free_left_inject; eauto. admit. admit.
  (* show that no valid location points into the stack block being freed *)
  admit.
+ (* turned into a call *)
  left; econstructor; split.
  eapply plus_one. eapply exec_Icall; eauto.
  eapply sig_function_translated; eauto.
  econstructor; eauto.
  eapply match_stacks_untailcall; eauto.
  eapply match_stacks_inside_invariant; eauto.
    intros. eapply Mem.perm_free_list; eauto.
  admit.
  eapply agree_val_regs; eauto.
  eapply Mem.free_left_inject; eauto. admit.
+ (* inlined *)
  assert (EQ: fd = Internal f0) by (eapply find_inlined_function; eauto).
  subst fd.
  right; split. simpl; lia. split. auto.
  econstructor; eauto.
  eapply match_stacks_inside_inlined_tailcall; eauto.
  eapply match_stacks_inside_invariant; eauto.
    intros. eapply Mem.perm_free_list; eauto.
  apply agree_val_regs_gen; auto.
  eapply Mem.free_left_inject; eauto. admit.

- (* builtin *)
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
  exploit match_stacks_inside_globalenvs; eauto. intros [bound MG].
  exploit tr_builtin_args; eauto. intros (vargs' & P & Q).
  exploit external_call_mem_inject; eauto.
    eapply match_stacks_inside_globals; eauto.
  intros [F1 [v1 [m1' [A [B [C [D [E [J K]]]]]]]]].
  left; econstructor; split.
  eapply plus_one. eapply exec_Ibuiltin; eauto.
    eapply external_call_symbols_preserved; eauto. apply senv_preserved.
  econstructor.
    eapply match_stacks_inside_set_res.
    eapply match_stacks_inside_extcall with (F1 := F) (F2 := F1) (m1 := m) (m1' := m'0); eauto.
    admit.
  auto. eauto. auto.
  destruct res; simpl; [apply agree_set_reg;auto|idtac|idtac]; eapply agree_regs_incr; eauto.
  auto. auto.
  eapply meminj_stack_vars_invariant; eauto.
  auto.
  admit.
- (* cond *)
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
  assert (eval_condition cond rs'##(sregs ctx args) m' = Some b).
    eapply eval_condition_inject; eauto. eapply agree_val_regs; eauto.
  left; econstructor; split.
  eapply plus_one. eapply exec_Icond; eauto.
  destruct b; econstructor; eauto.

- (* jumptable *)
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
  assert (Val.inject F rs#arg rs'#(sreg ctx arg)). eapply agree_val_reg; eauto.
  rewrite H0 in H2; inv H2.
  left; econstructor; split.
  eapply plus_one. eapply exec_Ijumptable; eauto.
  rewrite list_nth_z_map. rewrite H1. simpl; reflexivity.
  econstructor; eauto.

- (* return *)
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
+ (* not inlined *)
  inv MS0; try congruence.
  assert (X: { m1' | Mem.free_list m'0 (Venv.blocks_of_venv ve' (fn_stackspaces f')) = Some m1'}). admit.
  destruct X as [m1' FREE].
  left; econstructor; split.
  eapply plus_one. eapply exec_Ireturn; eauto.
  econstructor; eauto.
  eapply match_stacks_bound with (bound := (Venv.baseblock ve')).
  eapply match_stacks_invariant; eauto.
    intros. eapply Mem.perm_free_list; eauto.
    admit.
    intros. eapply Mem.perm_free_list; eauto.
  admit.
  destruct or; simpl. apply agree_val_reg; auto. auto.
  eapply Mem.free_right_inject; eauto. eapply Mem.free_left_inject; eauto. admit. admit.
  (* show that no valid location points into the stack block being freed *)
  intros. inversion FB; subst.
  admit.

+ (* inlined *)
  right. split. simpl. lia. split. auto.
  econstructor; eauto.
  eapply match_stacks_inside_invariant; eauto.
    intros. eapply Mem.perm_free_list; eauto.
  destruct or; simpl. apply agree_val_reg; auto. auto.
  eapply Mem.free_left_inject; eauto. admit.

- (* internal function, not inlined *)
  assert (A: exists f', tr_function cunit f f' /\ fd' = Internal f'). admit.
  destruct A as [f' [TR1 EQ]].
  assert (TR: tr_function prog f f').
  { eapply tr_function_linkorder; eauto. }
  inversion TR; subst. admit.
  (* exploit Mem.alloc_parallel_inject. eauto. eauto. apply Z.le_refl. *)
  (*   instantiate (1 := fn_stacksize f'). inv H1. extlia. *)
  (* intros [F' [m1' [sp' [A [B [C [D E]]]]]]]. *)
  (* left; econstructor; split. *)
  (* eapply plus_one. eapply exec_function_internal; eauto. *)
  (* rewrite H6. econstructor. *)
  (* instantiate (1 := F'). apply match_stacks_inside_base. *)
  (* assert (SP: sp' = Mem.nextblock m'0) by (eapply Mem.alloc_result; eauto). *)
  (* rewrite <- SP in MS0. *)
  (* eapply match_stacks_invariant; eauto. *)
  (*   intros. destruct (eq_block b1 stk). *)
  (*   subst b1. rewrite D in H8; inv H8. eelim Plt_strict; eauto. *)
  (*   rewrite E in H8; auto. *)
  (*   intros. exploit Mem.perm_alloc_inv. eexact H. eauto. *)
  (*   destruct (eq_block b1 stk); intros; auto. *)
  (*   subst b1. rewrite D in H8; inv H8. eelim Plt_strict; eauto. *)
  (*   intros. eapply Mem.perm_alloc_1; eauto. *)
  (*   intros. exploit Mem.perm_alloc_inv. eexact A. eauto. *)
  (*   rewrite dec_eq_false; auto with ordered_type. *)
  (* auto. auto. auto. eauto. auto. *)
  (* rewrite H5. apply agree_regs_init_regs. eauto. auto. inv H1; auto. congruence. auto. *)
  (* eapply Mem.valid_new_block; eauto. *)
  (* red; intros. split. *)
  (* eapply Mem.perm_alloc_2; eauto. inv H1; extlia. *)
  (* intros; red; intros. exploit Mem.perm_alloc_inv. eexact H. eauto. *)
  (* destruct (eq_block b stk); intros. *)
  (* subst. rewrite D in H9; inv H9. inv H1; extlia. *)
  (* rewrite E in H9; auto. eelim Mem.fresh_block_alloc. eexact A. eapply Mem.mi_mappedblocks; eauto. *)
  (* auto. *)
  (* intros. exploit Mem.perm_alloc_inv; eauto. rewrite dec_eq_true. lia. *)

- (* internal function, inlined *)
  inversion FB; subst. admit.
  (* exploit Mem.alloc_left_mapped_inject. *)
  (*   eauto. *)
  (*   eauto. *)
  (*   (* sp' is valid *) *)
  (*   instantiate (1 := sp'). auto. *)
  (*   (* offset is representable *) *)
  (*   instantiate (1 := dstk ctx). generalize (Z.le_max_r (fn_stacksize f) 0). lia. *)
  (*   (* size of target block is representable *) *)
  (*   intros. right. exploit SSZ2; eauto with mem. inv FB; lia. *)
  (*   (* we have full permissions on sp' at and above dstk ctx *) *)
  (*   intros. apply Mem.perm_cur. apply Mem.perm_implies with Freeable; auto with mem. *)
  (*   eapply range_private_perms; eauto. extlia. *)
  (*   (* offset is aligned *) *)
  (*   replace (fn_stacksize f - 0) with (fn_stacksize f) by lia. *)
  (*   inv FB. apply min_alignment_sound; auto. *)
  (*   (* nobody maps to (sp, dstk ctx...) *) *)
  (*   intros. exploit (PRIV (ofs + delta')); eauto. extlia. *)
  (*   intros [A B]. eelim B; eauto. *)
  (*   replace (ofs + delta' - delta') with ofs by lia. *)
  (*   apply Mem.perm_max with k. apply Mem.perm_implies with p; auto with mem. *)
  (* intros [F' [A [B [C D]]]]. *)
  (* exploit tr_moves_init_regs; eauto. intros [rs'' [P [Q R]]]. *)
  (* left; econstructor; split. *)
  (* eapply plus_left. eapply exec_Inop; eauto. eexact P. traceEq. *)
  (* econstructor. *)
  (* eapply match_stacks_inside_alloc_left; eauto. *)
  (* eapply match_stacks_inside_invariant; eauto. *)
  (* lia. *)
  (* eauto. auto. *)
  (* apply agree_regs_incr with F; auto. *)
  (* auto. auto. auto. *)
  (* rewrite H2. eapply range_private_alloc_left; eauto. *)
  (* auto. auto. *)

- (* external function *)
  exploit match_stacks_globalenvs; eauto. intros [bound MG].
  exploit external_call_mem_inject; eauto.
    eapply match_globalenvs_preserves_globals; eauto.
  intros [F1 [v1 [m1' [A [B [C [D [E [J K]]]]]]]]].
  simpl in FD. inv FD.
  left; econstructor; split.
  eapply plus_one. eapply exec_function_external; eauto.
    eapply external_call_symbols_preserved; eauto. apply senv_preserved.
  econstructor.
    eapply match_stacks_bound with (Mem.nextblock m'0).
    eapply match_stacks_extcall with (F1 := F) (F2 := F1) (m1 := m) (m1' := m'0); eauto.
    extlia.
    eapply external_call_nextblock; eauto.
    auto. auto.

- (* return from noninlined function *)
  inv MS0.
+ (* normal case *)
  left; econstructor; split.
  eapply plus_one. eapply exec_return.
  econstructor; eauto.
  apply match_stacks_inside_set_reg; auto.
  apply agree_set_reg; auto.
  intros. pose proof (Venv.checkpoint_order ve').
  unfold Venv.valid_block in H. destruct H.
  apply Plt_Ple_trans with (r := Mem.nextblock m') in H1.
  auto. extlia.
+ (* untailcall case *)
  inv MS; try congruence.
  rewrite RET in RET0; inv RET0.
  left; econstructor; split.
  eapply plus_one. eapply exec_return.
  eapply match_regular_states.
  eapply match_stacks_inside_set_reg; eauto.
  eauto. auto.
  apply agree_set_reg; auto.
  auto. auto. auto.
  intros. pose proof (Venv.checkpoint_order ve').
  unfold Venv.valid_block in H. destruct H.
  apply Plt_Ple_trans with (r := Mem.nextblock m') in H1.
  auto. extlia.

- (* return from inlined function *)
  inv MS0; try congruence. rewrite RET0 in RET; inv RET.
  unfold inline_return in AT.
  destruct or.
+ (* with a result *)
  left; econstructor; split.
  eapply plus_one. eapply exec_Iop; eauto. simpl. reflexivity.
  econstructor; eauto. apply match_stacks_inside_set_reg; auto. apply agree_set_reg; auto.
+ (* without a result *)
  left; econstructor; split.
  eapply plus_one. eapply exec_Inop; eauto.
  econstructor; eauto. subst vres. apply agree_set_reg_undef'; auto.
Admitted.

Lemma transf_initial_states:
  forall st1, initial_state prog st1 -> exists st2, initial_state tprog st2 /\ match_states st1 st2.
Proof.
  intros. inv H.
  exploit function_ptr_translated; eauto. intros (cu & tf & FIND & TR & LINK).
  exists (Callstate nil tf nil m0); split.
  econstructor; eauto.
    eapply (Genv.init_mem_match TRANSF); eauto.
    rewrite symbols_preserved. replace (prog_main tprog) with (prog_main prog). auto.
    symmetry; eapply match_program_main; eauto.
    rewrite <- H3. eapply sig_function_translated; eauto.
  econstructor; eauto.
  instantiate (1 := Mem.flat_inj (Mem.nextblock m0)).
  apply match_stacks_nil with (Mem.nextblock m0).
  constructor; intros.
    unfold Mem.flat_inj. apply pred_dec_true; auto.
    unfold Mem.flat_inj in H. destruct (plt b1 (Mem.nextblock m0)); congruence.
    eapply Genv.find_symbol_not_fresh; eauto.
    eapply Genv.find_funct_ptr_not_fresh; eauto.
    eapply Genv.find_var_info_not_fresh; eauto.
    apply Ple_refl.
  eapply Genv.initmem_inject; eauto.
Qed.

Lemma transf_final_states:
  forall st1 st2 r,
  match_states st1 st2 -> final_state st1 r -> final_state st2 r.
Proof.
  intros. inv H0. inv H.
  exploit match_stacks_empty; eauto. intros EQ; subst. inv VINJ. constructor.
  exploit match_stacks_inside_empty; eauto. intros [A B]. congruence.
Qed.

Theorem transf_program_correct:
  forward_simulation (semantics prog) (semantics tprog).
Proof.
  eapply forward_simulation_star.
  apply senv_preserved.
  eexact transf_initial_states.
  eexact transf_final_states.
  eexact step_simulation.
Qed.

End INLINING.
