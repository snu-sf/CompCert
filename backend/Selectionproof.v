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

(** Correctness of instruction selection *)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Errors.
Require Import Integers.
Require Import Values.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Language.
Require Import Switch.
Require Import Cminor.
Require Import Op.
Require Import CminorSel.
Require Import SelectOp.
Require Import SelectDiv.
Require Import SelectLong.
Require Import Selection.
Require Import SelectOpproof.
Require Import SelectDivproof.
Require Import SelectLongproof.
Require Import MapsExtra.
Require Import Linker.
Require Import LinkerProp.
Require Import Linkeq.
Require Import SepcompRel.
Require Import CoqlibExtra.

Local Open Scope cminorsel_scope.
Local Open Scope error_monad_scope.


(** * Correctness of the instruction selection functions for expressions *)

Section PRESERVATION.

Variable prog: Cminor.program.
Variable tprog: CminorSel.program.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.
Hypothesis HELPERS:
  forall name sg, In (name, sg) i64_helpers -> helper_declared ge name sg.
Hypothesis TRANSF:
  @sepcomp_rel
    Language_Cminor Language_CminorSel
    (fun p f tf =>
       sel_function (Genv.globalenv p) f = OK tf)
    (fun p ef tef =>
       ef = tef)
    (@OK _)
    prog tprog.

Let prog_match:
  match_program
    (fun fd tfd =>
       exists sprog, program_linkeq Language_Cminor sprog prog /\
       sel_fundef (Genv.globalenv sprog) fd = OK tfd)
    (fun info tinfo => info = tinfo)
    nil prog.(prog_main)
    prog tprog.
Proof.
  destruct prog as [defs ?], tprog as [tdefs ?]. clear HELPERS.
  inv TRANSF. simpl in *. subst. clear ge tge.
  revert tdefs Hdefs. generalize defs at 1 3 as fdefs.
  induction defs; intros fdefs tdefs Hdefs.
  { inv Hdefs. constructor; auto. exists nil. split; auto. constructor. }
  inv Hdefs. destruct a, b1, H1 as [? H1]. simpl in *. subst.
  eapply IHdefs in H3. destruct H3 as [H3 ?]. split; [|auto].
  destruct H3 as [? H3]. simpl in *. rewrite app_nil_r in *.
  destruct H3 as [H3 ?]. subst.
  eexists. rewrite app_nil_r. split; auto.
  constructor; auto.
  destruct H1 as [prog_src [Hprog_src H1]]. inv H1.
  - apply match_glob_fun. eexists. split; eauto.
    simpl in *. destruct fd_src; inv Hf_src. destruct fd_tgt; inv Hf_tgt.
    unfold sel_fundef, transf_partial_fundef. rewrite Hf. auto.
  - apply match_glob_fun. eexists. split; eauto.
    simpl in *. destruct fd_src; inv Hef_src. destruct fd_tgt; inv Hef_tgt.
    unfold sel_fundef, transf_partial_fundef. auto.
  - unfold transf_globvar in Hv. monadInv Hv. inv EQ.
    destruct gv_src. constructor. auto.
Qed.

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof.
  intros. eapply Genv.find_symbol_match; eauto.
Qed.

Lemma function_ptr_translated:
  forall (b: block) (f: Cminor.fundef),
  Genv.find_funct_ptr ge b = Some f ->
  exists tf, Genv.find_funct_ptr tge b = Some tf /\
  exists sprog, program_linkeq Language_Cminor sprog prog /\
  sel_fundef (Genv.globalenv sprog) f = OK tf.
Proof.  
  intros. exploit Genv.find_funct_ptr_match; eauto.
Qed.

Lemma functions_translated:
  forall (v v': val) (f: Cminor.fundef),
  Genv.find_funct ge v = Some f ->
  Val.lessdef v v' ->
  exists tf, Genv.find_funct tge v' = Some tf /\
  exists sprog, program_linkeq Language_Cminor sprog prog /\
  sel_fundef (Genv.globalenv sprog) f = OK tf.
Proof.  
  intros. exploit Genv.find_funct_match; eauto.
  intros [tf [Htf [sprog [Hsprog hf]]]].
  eexists; split; eauto.
  inv H0; auto. inv H.
Qed.

Lemma sig_function_translated:
  forall ge f tf, sel_fundef ge f = OK tf -> funsig tf = Cminor.funsig f.
Proof.
  intros. destruct f; monadInv H; auto. monadInv EQ. auto. 
Qed.

Lemma stackspace_function_translated:
  forall ge f tf, sel_function ge f = OK tf -> fn_stackspace tf = Cminor.fn_stackspace f.
Proof.
  intros. monadInv H. auto. 
Qed.

Lemma varinfo_preserved:
  forall b, Genv.find_var_info tge b = Genv.find_var_info ge b.
Proof.
  intros. destruct (Genv.find_var_info ge b) as [v|] eqn:V.
  - exploit Genv.find_var_info_match; eauto. intros [tv [A B]]. inv B. assumption.
  - destruct (Genv.find_var_info tge b) as [v'|] eqn:V'; auto.
    exploit Genv.find_var_info_rev_match; eauto.
    simpl. destruct (plt b (Genv.genv_next (Genv.globalenv prog))); try tauto.
    intros [v [A B]]. inv B. fold ge in A. congruence.
Qed.

Lemma helper_declared_preserved:
  forall id sg, helper_declared ge id sg -> helper_declared tge id sg.
Proof.
  intros id sg (b & A & B).
  exploit function_ptr_translated; eauto. simpl. intros (tf & P & Q). inv Q. 
  inv H. inv H1.
  exists b; split; auto. rewrite symbols_preserved. auto.
Qed.

Let HELPERS':
  forall name sg, In (name, sg) i64_helpers -> helper_declared tge name sg.
Proof.
  intros. apply helper_declared_preserved. auto.
Qed.

Section CMCONSTR.

Variable sp: val.
Variable e: env.
Variable m: mem.

Lemma eval_condexpr_of_expr:
  forall a le v b,
  eval_expr tge sp e m le a v ->
  Val.bool_of_val v b ->
  eval_condexpr tge sp e m le (condexpr_of_expr a) b.
Proof.
  intros until a. functional induction (condexpr_of_expr a); intros.
(* compare *)
  inv H. econstructor; eauto. 
  simpl in H6. inv H6. apply Val.bool_of_val_of_optbool. auto.
(* condition *)
  inv H. econstructor; eauto. destruct va; eauto.
(* let *)
  inv H. econstructor; eauto.
(* default *)
  econstructor. constructor. eauto. constructor. 
  simpl. inv H0. auto. auto. 
Qed.

Lemma eval_load:
  forall le a v chunk v',
  eval_expr tge sp e m le a v ->
  Mem.loadv chunk m v = Some v' ->
  eval_expr tge sp e m le (load chunk a) v'.
Proof.
  intros. generalize H0; destruct v; simpl; intro; try discriminate.
  unfold load. 
  generalize (eval_addressing _ _ _ _ _ chunk _ _ _ _ H (refl_equal _)).
  destruct (addressing chunk a). intros [vl [EV EQ]]. 
  eapply eval_Eload; eauto. 
Qed.

Lemma eval_store:
  forall chunk a1 a2 v1 v2 f k m',
  eval_expr tge sp e m nil a1 v1 ->
  eval_expr tge sp e m nil a2 v2 ->
  Mem.storev chunk m v1 v2 = Some m' ->
  step tge (State f (store chunk a1 a2) k sp e m)
        E0 (State f Sskip k sp e m').
Proof.
  intros. generalize H1; destruct v1; simpl; intro; try discriminate.
  unfold store.
  generalize (eval_addressing _ _ _ _ _ chunk _ _ _ _ H (refl_equal _)).
  destruct (addressing chunk a1). intros [vl [EV EQ]]. 
  eapply step_store; eauto. 
Qed.

(** Correctness of instruction selection for operators *)

Lemma eval_sel_unop:
  forall le op a1 v1 v,
  eval_expr tge sp e m le a1 v1 ->
  eval_unop op v1 = Some v ->
  exists v', eval_expr tge sp e m le (sel_unop op a1) v' /\ Val.lessdef v v'.
Proof.
  destruct op; simpl; intros; FuncInv; try subst v.
  apply eval_cast8unsigned; auto.
  apply eval_cast8signed; auto.
  apply eval_cast16unsigned; auto.
  apply eval_cast16signed; auto.
  apply eval_negint; auto.
  apply eval_notint; auto.
  apply eval_negf; auto.
  apply eval_absf; auto.
  apply eval_negfs; auto.
  apply eval_absfs; auto.
  apply eval_singleoffloat; auto.
  apply eval_floatofsingle; auto.
  eapply eval_intoffloat; eauto.
  eapply eval_intuoffloat; eauto.
  eapply eval_floatofint; eauto.
  eapply eval_floatofintu; eauto.
  eapply eval_intofsingle; eauto.
  eapply eval_intuofsingle; eauto.
  eapply eval_singleofint; eauto.
  eapply eval_singleofintu; eauto.
  eapply eval_negl; eauto.
  eapply eval_notl; eauto.
  eapply eval_intoflong; eauto.
  eapply eval_longofint; eauto.
  eapply eval_longofintu; eauto.
  eapply eval_longoffloat; eauto.
  eapply eval_longuoffloat; eauto.
  eapply eval_floatoflong; eauto.
  eapply eval_floatoflongu; eauto.
  eapply eval_longofsingle; eauto.
  eapply eval_longuofsingle; eauto.
  eapply eval_singleoflong; eauto.
  eapply eval_singleoflongu; eauto.
Qed.

Lemma eval_sel_binop:
  forall le op a1 a2 v1 v2 v,
  eval_expr tge sp e m le a1 v1 ->
  eval_expr tge sp e m le a2 v2 ->
  eval_binop op v1 v2 m = Some v ->
  exists v', eval_expr tge sp e m le (sel_binop op a1 a2) v' /\ Val.lessdef v v'.
Proof.
  destruct op; simpl; intros; FuncInv; try subst v.
  apply eval_add; auto.
  apply eval_sub; auto.
  apply eval_mul; auto.
  eapply eval_divs; eauto.
  eapply eval_divu; eauto.
  eapply eval_mods; eauto.
  eapply eval_modu; eauto.
  apply eval_and; auto.
  apply eval_or; auto.
  apply eval_xor; auto.
  apply eval_shl; auto.
  apply eval_shr; auto.
  apply eval_shru; auto.
  apply eval_addf; auto.
  apply eval_subf; auto.
  apply eval_mulf; auto.
  apply eval_divf; auto.
  apply eval_addfs; auto.
  apply eval_subfs; auto.
  apply eval_mulfs; auto.
  apply eval_divfs; auto.
  eapply eval_addl; eauto.
  eapply eval_subl; eauto.
  eapply eval_mull; eauto.
  eapply eval_divl; eauto.
  eapply eval_divlu; eauto.
  eapply eval_modl; eauto.
  eapply eval_modlu; eauto.
  eapply eval_andl; eauto.
  eapply eval_orl; eauto.
  eapply eval_xorl; eauto.
  eapply eval_shll; eauto.
  eapply eval_shrl; eauto.
  eapply eval_shrlu; eauto.
  apply eval_comp; auto.
  apply eval_compu; auto.
  apply eval_compf; auto.
  apply eval_compfs; auto.
  exists v; split; auto. eapply eval_cmpl; eauto.
  exists v; split; auto. eapply eval_cmplu; eauto.
Qed.

End CMCONSTR.

(** Recognition of calls to built-in functions *)

Lemma expr_is_addrof_ident_correct:
  forall e id,
  expr_is_addrof_ident e = Some id ->
  e = Cminor.Econst (Cminor.Oaddrsymbol id Int.zero).
Proof.
  intros e id. unfold expr_is_addrof_ident. 
  destruct e; try congruence.
  destruct c; try congruence.
  predSpec Int.eq Int.eq_spec i0 Int.zero; congruence.
Qed.

Lemma find_symbol_spec (p:Cminor.program) i:
  match Genv.find_symbol (Genv.globalenv p) i, option_map snd (find (fun id => peq i (fst id)) (rev p.(prog_defs))) with
    | Some b, Some g =>
      match
        g,
        Genv.find_funct_ptr (Genv.globalenv p) b,
        Genv.find_var_info (Genv.globalenv p) b
      with
        | Gfun fd1, Some fd2, None => fd1 = fd2
        | Gvar vi1, None, Some vi2 => vi1 = vi2
        | _, _, _ => False
      end
    | None, None => True
    | _, _ => False
  end.
Proof.
  Ltac clarify :=
    repeat (try match goal with
                  | [H1: ?m ! ?b = _, H2: ?m ! ?b = _ |- _] => rewrite H1 in H2; inv H2
                  | [H: Some _ = Some _ |- _] => inv H
                  | [|- context[(PTree.set ?k _ _) ! ?k]] => rewrite PTree.gss
                  | [H: context[(PTree.set ?k _ _) ! ?k] |- _] => rewrite PTree.gss in H
                  | [|- context[(PTree.set _ _ _) ! _]] => rewrite PTree.gsspec
                  | [H: context[(PTree.set _ _ _) ! _] |- _] => rewrite PTree.gsspec in H
                  | [|- context[peq ?a ?b]] => destruct (peq a b)
                  | [H: context[peq ?a ?b] |- _] => destruct (peq a b)
                  | [H: context[match ?x with | Some _ => _ | None => _ end] |- _] =>
                    let H := fresh "H" in destruct x eqn:H
                  | [|- context[match ?x with | Some _ => _ | None => _ end]] =>
                    let H := fresh "H" in destruct x eqn:H
                  | [H: False |- _] => inv H
                  | [g: globdef _ _ |- _] => destruct g
                end; subst; auto).
  destruct p as [defs main]. unfold Genv.globalenv. simpl in *.
  unfold Genv.add_globals. rewrite <- fold_left_rev_right.
  unfold Genv.find_symbol, Genv.find_funct_ptr, Genv.find_var_info.
  induction (rev defs); simpl.
  { rewrite PTree.gempty. auto. }
  rewrite ? PTree.gsspec. destruct a. simpl. destruct (peq i i0); [subst|]; simpl.
  { destruct g; clarify.
    - apply Genv.genv_vars_range in H3. xomega.
    - apply Genv.genv_vars_range in H3. xomega.
    - apply Genv.genv_vars_range in H1. xomega.
    - apply Genv.genv_funs_range in H3. xomega.
    - apply Genv.genv_funs_range in H3. xomega.
    - apply Genv.genv_funs_range in H1. xomega.
  }
  { clarify.
    - apply Genv.genv_funs_range in H1. xomega.
    - apply Genv.genv_funs_range in H1. xomega.
    - apply Genv.genv_funs_range in H1. xomega.
    - apply Genv.genv_vars_range in H2. xomega.
    - apply Genv.genv_vars_range in H2. xomega.
    - apply Genv.genv_vars_range in H2. xomega.
  }
Qed.

Lemma classify_call_correct:
  forall sp e m a v fd,
  Cminor.eval_expr ge sp e m a v ->
  Genv.find_funct ge v = Some fd ->
  match classify_call ge a with
  | Call_default => True
  | Call_imm id => exists b, Genv.find_symbol ge id = Some b /\ v = Vptr b Int.zero
  | Call_builtin ef => fd = External ef
  end.
Proof.
  unfold classify_call; intros. 
  destruct (expr_is_addrof_ident a) as [id|] eqn:?. 
  exploit expr_is_addrof_ident_correct; eauto. intros EQ; subst a.
  inv H. inv H2. 
  destruct (Genv.find_symbol ge id) as [b|] eqn:?. 
  rewrite Genv.find_funct_find_funct_ptr in H0. 
  rewrite H0. 
  destruct fd. exists b; auto. 
  destruct (ef_inline e0). auto. exists b; auto.
  simpl in H0. discriminate.
  auto.
Qed.

Lemma classify_call_correct_ext:
  forall sp e m a v fd sprog
  (SPROG: program_linkeq Language_Cminor sprog prog),
  Cminor.eval_expr ge sp e m a v ->
  Genv.find_funct ge v = Some fd ->
  match classify_call (Genv.globalenv sprog) a with
  | Call_default => True
  | Call_imm id => exists b, Genv.find_symbol ge id = Some b /\ v = Vptr b Int.zero
  | Call_builtin ef => fd = External ef
  end.
Proof.
  intros. exploit classify_call_correct; eauto.
  unfold ge, tge in *. clear ge tge.
  unfold classify_call. destruct (expr_is_addrof_ident a) eqn:Hident; auto.
  destruct SPROG as [SPROG _]. unfold Cminor.fundef in *. simpl in *.
  generalize (find_symbol_spec prog i).
  generalize (find_symbol_spec sprog i).
  unfold Cminor.fundef in *.
  destruct (Genv.find_symbol (Genv.globalenv sprog) i) as [b_src|] eqn:Hb_src.
  - match goal with
      | [|- context[match ?g with | Some _ => _ | None => _ end -> _]] =>
        let H := fresh "H" in destruct g as [g_src|] eqn:H; [|intro X; inv X]
    end.
    exploit (SPROG i); [rewrite PTree_guespec; apply H1|]. intros [g_tgt [Hg_tgt Hsim]].
    rewrite PTree_guespec in Hg_tgt. unfold ident, Cminor.fundef in *. simpl in *. rewrite Hg_tgt.
    inv Hsim.
    + destruct (Genv.find_funct_ptr (Genv.globalenv sprog) b_src) eqn:Hfd_src; [|intro X; inv X].
      destruct (Genv.find_var_info (Genv.globalenv sprog) b_src) eqn:Hvi_src; [intro X; inv X|].
      intro. subst. fold Cminor.fundef in *.
      destruct (Genv.find_symbol (Genv.globalenv prog) i) eqn:Hb_tgt; [|intro X; inv X].
      destruct (Genv.find_funct_ptr (Genv.globalenv prog) b) eqn:Hfd'_src; [|intro X; inv X].
      destruct (Genv.find_var_info (Genv.globalenv prog) b) eqn:Hvi'_src; [intro X; inv X|].
      intro. subst. fold Cminor.fundef in *.
      inv Hv; auto. inv H2.
      * destruct f; inv H3. destruct f0; inv H4. destruct e1; inv Hlinkable. auto.
      * destruct f; inv H3. destruct f0; inv H4. auto.
    + destruct (Genv.find_funct_ptr (Genv.globalenv sprog) b_src) eqn:Hfd_src; [intro X; inv X|].
      destruct (Genv.find_var_info (Genv.globalenv sprog) b_src) eqn:Hvi_src; [|intro X; inv X].
      intro. subst. fold Cminor.fundef in *.
      destruct (Genv.find_symbol (Genv.globalenv prog) i) eqn:Hb_tgt; [|intro X; inv X].
      destruct (Genv.find_funct_ptr (Genv.globalenv prog) b) eqn:Hfd'_src; [intro X; inv X|].
      destruct (Genv.find_var_info (Genv.globalenv prog) b) eqn:Hvi'_src; [|intro X; inv X].
      intros ? [b' [Hb' Hv']]. subst. rewrite Hb_tgt in Hb'. inv Hb'.
      eexists. split; eauto.
  - match goal with
      | [|- context[match ?g with | Some _ => _ | None => _ end -> _]] =>
        let H := fresh "H" in destruct g as [g_src|] eqn:H; intro X; inv X
    end.
    fold Cminor.fundef in *.
    destruct (Genv.find_symbol (Genv.globalenv prog) i) eqn:Hb_tgt.
    { match goal with
        | [|- context[match ?g with | Some _ => _ | None => _ end -> _]] =>
          let H := fresh "H" in destruct g as [g_tgt|] eqn:H; [|intro X; inv X]
      end.
      destruct g_tgt as [fd_tgt|vi_tgt].
      { destruct (Genv.find_funct_ptr (Genv.globalenv prog) b) eqn:Hfd_tgt; [|intro X; inv X].
        destruct (Genv.find_var_info (Genv.globalenv prog) b) eqn:Hvi_tgt; [intro X; inv X|].
        intro. subst. destruct f.
        { rewrite Hb_tgt. auto. }
        { destruct (ef_inline e0) eqn:Hinline.
          { intro. subst. eexists. split; eauto.
            destruct a; inv Hident. destruct c; inv H4. destruct (Int.eq i1 Int.zero); inv H5.
            destruct v; inv H0. destruct (Int.eq_dec i0 Int.zero); inv H4.
            inv H. inv H4. unfold Cminor.fundef in *. simpl in *. rewrite Hb_tgt in *.
            inv H0. auto.
          }
          { rewrite Hb_tgt. auto. }
        }
      }
      { destruct (Genv.find_funct_ptr (Genv.globalenv prog) b); [intro X; inv X|].
        destruct (Genv.find_var_info (Genv.globalenv prog) b) eqn:Hvi_tgt; [|intro X; inv X].
        intro. subst. rewrite Hb_tgt. auto.
      }
    }
    { rewrite Hb_tgt. auto. }
Qed.

(** Translation of [switch] statements *)

Inductive Rint: Z -> val -> Prop :=
  | Rint_intro: forall n, Rint (Int.unsigned n) (Vint n).

Inductive Rlong: Z -> val -> Prop :=
  | Rlong_intro: forall n, Rlong (Int64.unsigned n) (Vlong n).

Section SEL_SWITCH.

Variable make_cmp_eq: expr -> Z -> expr.
Variable make_cmp_ltu: expr -> Z -> expr.
Variable make_sub: expr -> Z -> expr.
Variable make_to_int: expr -> expr.
Variable modulus: Z.
Variable R: Z -> val -> Prop.

Hypothesis eval_make_cmp_eq: forall sp e m le a v i n,
  eval_expr tge sp e m le a v -> R i v -> 0 <= n < modulus ->
  eval_expr tge sp e m le (make_cmp_eq a n) (Val.of_bool (zeq i n)).
Hypothesis eval_make_cmp_ltu: forall sp e m le a v i n,
  eval_expr tge sp e m le a v -> R i v -> 0 <= n < modulus ->
  eval_expr tge sp e m le (make_cmp_ltu a n) (Val.of_bool (zlt i n)).
Hypothesis eval_make_sub: forall sp e m le a v i n,
  eval_expr tge sp e m le a v -> R i v -> 0 <= n < modulus ->
  exists v', eval_expr tge sp e m le (make_sub a n) v' /\ R ((i - n) mod modulus) v'.
Hypothesis eval_make_to_int: forall sp e m le a v i,
  eval_expr tge sp e m le a v -> R i v ->
  exists v', eval_expr tge sp e m le (make_to_int a) v' /\ Rint (i mod Int.modulus) v'.

Lemma sel_switch_correct_rec:
  forall sp e m varg i x,
  R i varg ->
  forall t arg le,
  wf_comptree modulus t ->
  nth_error le arg = Some varg ->
  comptree_match modulus i t = Some x ->
  eval_exitexpr tge sp e m le (sel_switch make_cmp_eq make_cmp_ltu make_sub make_to_int arg t) x.
Proof.
  intros until x; intros Ri. induction t; simpl; intros until le; intros WF ARG MATCH.
- (* base case *)
  inv MATCH. constructor.
- (* eq test *)
  inv WF.
  assert (eval_expr tge sp e m le (make_cmp_eq (Eletvar arg) key) (Val.of_bool (zeq i key))).
  { eapply eval_make_cmp_eq; eauto. constructor; auto. }
  eapply eval_XEcondition with (va := zeq i key). 
  eapply eval_condexpr_of_expr; eauto. destruct (zeq i key); constructor; auto. 
  destruct (zeq i key); simpl. 
  + inv MATCH. constructor.
  + eapply IHt; eauto.
- (* lt test *)
  inv WF.
  assert (eval_expr tge sp e m le (make_cmp_ltu (Eletvar arg) key) (Val.of_bool (zlt i key))).
  { eapply eval_make_cmp_ltu; eauto. constructor; auto. }
  eapply eval_XEcondition with (va := zlt i key). 
  eapply eval_condexpr_of_expr; eauto. destruct (zlt i key); constructor; auto. 
  destruct (zlt i key); simpl. 
  + eapply IHt1; eauto.
  + eapply IHt2; eauto.
- (* jump table *)
  inv WF.
  exploit (eval_make_sub sp e m le). eapply eval_Eletvar. eauto. eauto.
  instantiate (1 := ofs). auto.
  intros (v' & A & B).
  set (i' := (i - ofs) mod modulus) in *.
  assert (eval_expr tge sp e m (v' :: le) (make_cmp_ltu (Eletvar O) sz) (Val.of_bool (zlt i' sz))).
  { eapply eval_make_cmp_ltu; eauto. constructor; auto. }
  econstructor. eauto. 
  eapply eval_XEcondition with (va := zlt i' sz).
  eapply eval_condexpr_of_expr; eauto. destruct (zlt i' sz); constructor; auto.
  destruct (zlt i' sz); simpl.
  + exploit (eval_make_to_int sp e m (v' :: le) (Eletvar O)).
    constructor. simpl; eauto. eauto. intros (v'' & C & D). inv D. 
    econstructor; eauto. congruence. 
  + eapply IHt; eauto.
Qed.

Lemma sel_switch_correct:
  forall dfl cases arg sp e m varg i t le,
  validate_switch modulus dfl cases t = true ->
  eval_expr tge sp e m le arg varg ->
  R i varg ->
  0 <= i < modulus ->
  eval_exitexpr tge sp e m le
     (XElet arg (sel_switch make_cmp_eq make_cmp_ltu make_sub make_to_int O t))
     (switch_target i dfl cases).
Proof.
  intros. exploit validate_switch_correct; eauto. omega. intros [A B].
  econstructor. eauto. eapply sel_switch_correct_rec; eauto.
Qed.

End SEL_SWITCH.

Lemma sel_switch_int_correct:
  forall dfl cases arg sp e m i t le,
  validate_switch Int.modulus dfl cases t = true ->
  eval_expr tge sp e m le arg (Vint i) ->
  eval_exitexpr tge sp e m le (XElet arg (sel_switch_int O t)) (switch_target (Int.unsigned i) dfl cases).
Proof.
  assert (INTCONST: forall n sp e m le, 
            eval_expr tge sp e m le (Eop (Ointconst n) Enil) (Vint n)).
  { intros. econstructor. constructor. auto. } 
  intros. eapply sel_switch_correct with (R := Rint); eauto.
- intros until n; intros EVAL R RANGE.
  exploit eval_comp. eexact EVAL. apply (INTCONST (Int.repr n)).  
  instantiate (1 := Ceq). intros (vb & A & B). 
  inv R. unfold Val.cmp in B. simpl in B. revert B. 
  predSpec Int.eq Int.eq_spec n0 (Int.repr n); intros B; inv B. 
  rewrite Int.unsigned_repr. unfold proj_sumbool; rewrite zeq_true; auto. 
  unfold Int.max_unsigned; omega.
  unfold proj_sumbool; rewrite zeq_false; auto.
  red; intros; elim H1. rewrite <- (Int.repr_unsigned n0). congruence.
- intros until n; intros EVAL R RANGE.
  exploit eval_compu. eexact EVAL. apply (INTCONST (Int.repr n)).  
  instantiate (1 := Clt). intros (vb & A & B). 
  inv R. unfold Val.cmpu in B. simpl in B.
  unfold Int.ltu in B. rewrite Int.unsigned_repr in B. 
  destruct (zlt (Int.unsigned n0) n); inv B; auto. 
  unfold Int.max_unsigned; omega.
- intros until n; intros EVAL R RANGE.
  exploit eval_sub. eexact EVAL. apply (INTCONST (Int.repr n)). intros (vb & A & B).
  inv R. simpl in B. inv B. econstructor; split; eauto. 
  replace ((Int.unsigned n0 - n) mod Int.modulus)
     with (Int.unsigned (Int.sub n0 (Int.repr n))).
  constructor.
  unfold Int.sub. rewrite Int.unsigned_repr_eq. f_equal. f_equal. 
  apply Int.unsigned_repr. unfold Int.max_unsigned; omega.
- intros until i0; intros EVAL R. exists v; split; auto. 
  inv R. rewrite Zmod_small by (apply Int.unsigned_range). constructor.
- constructor. 
- apply Int.unsigned_range.
Qed.

Lemma sel_switch_long_correct:
  forall dfl cases arg sp e m i t le,
  validate_switch Int64.modulus dfl cases t = true ->
  eval_expr tge sp e m le arg (Vlong i) ->
  eval_exitexpr tge sp e m le (XElet arg (sel_switch_long O t)) (switch_target (Int64.unsigned i) dfl cases).
Proof.
  intros. eapply sel_switch_correct with (R := Rlong); eauto.
- intros until n; intros EVAL R RANGE.
  eapply eval_cmpl. eexact EVAL. apply eval_longconst with (n := Int64.repr n).
  inv R. unfold Val.cmpl. simpl. f_equal; f_equal. unfold Int64.eq. 
  rewrite Int64.unsigned_repr. destruct (zeq (Int64.unsigned n0) n); auto. 
  unfold Int64.max_unsigned; omega.
- intros until n; intros EVAL R RANGE. 
  eapply eval_cmplu. eexact EVAL. apply eval_longconst with (n := Int64.repr n).
  inv R. unfold Val.cmplu. simpl. f_equal; f_equal. unfold Int64.ltu. 
  rewrite Int64.unsigned_repr. destruct (zlt (Int64.unsigned n0) n); auto. 
  unfold Int64.max_unsigned; omega.
- intros until n; intros EVAL R RANGE.
  exploit eval_subl.  eexact EVAL. apply eval_longconst with (n := Int64.repr n).
  intros (vb & A & B).
  inv R. simpl in B. inv B. econstructor; split; eauto. 
  replace ((Int64.unsigned n0 - n) mod Int64.modulus)
     with (Int64.unsigned (Int64.sub n0 (Int64.repr n))).
  constructor.
  unfold Int64.sub. rewrite Int64.unsigned_repr_eq. f_equal. f_equal. 
  apply Int64.unsigned_repr. unfold Int64.max_unsigned; omega.
- intros until i0; intros EVAL R. 
  exploit eval_lowlong. eexact EVAL. intros (vb & A & B). 
  inv R. simpl in B. inv B. econstructor; split; eauto.
  replace (Int64.unsigned n mod Int.modulus) with (Int.unsigned (Int64.loword n)).
  constructor.
  unfold Int64.loword. apply Int.unsigned_repr_eq. 
- constructor. 
- apply Int64.unsigned_range.
Qed.

(** Compatibility of evaluation functions with the "less defined than" relation. *)

Ltac TrivialExists :=
  match goal with
  | [ |- exists v, Some ?x = Some v /\ _ ] => exists x; split; auto
  | _ => idtac
  end.

Lemma eval_unop_lessdef:
  forall op v1 v1' v,
  eval_unop op v1 = Some v -> Val.lessdef v1 v1' ->
  exists v', eval_unop op v1' = Some v' /\ Val.lessdef v v'.
Proof.
  intros until v; intros EV LD. inv LD. 
  exists v; auto.
  destruct op; simpl in *; inv EV; TrivialExists.
Qed.

Lemma eval_binop_lessdef:
  forall op v1 v1' v2 v2' v m m',
  eval_binop op v1 v2 m = Some v -> 
  Val.lessdef v1 v1' -> Val.lessdef v2 v2' -> Mem.extends m m' ->
  exists v', eval_binop op v1' v2' m' = Some v' /\ Val.lessdef v v'.
Proof.
  intros until m'; intros EV LD1 LD2 ME.
  assert (exists v', eval_binop op v1' v2' m = Some v' /\ Val.lessdef v v').
  inv LD1. inv LD2. exists v; auto. 
  destruct op; destruct v1'; simpl in *; inv EV; TrivialExists.
  destruct op; simpl in *; inv EV; TrivialExists.
  destruct op; try (exact H). 
  simpl in *. TrivialExists. inv EV. apply Val.of_optbool_lessdef. 
  intros. apply Val.cmpu_bool_lessdef with (Mem.valid_pointer m) v1 v2; auto.
  intros; eapply Mem.valid_pointer_extends; eauto.
Qed.

(** * Semantic preservation for instruction selection. *)

(** Relationship between the local environments. *)

Definition env_lessdef (e1 e2: env) : Prop :=
  forall id v1, e1!id = Some v1 -> exists v2, e2!id = Some v2 /\ Val.lessdef v1 v2.

Lemma set_var_lessdef:
  forall e1 e2 id v1 v2,
  env_lessdef e1 e2 -> Val.lessdef v1 v2 ->
  env_lessdef (PTree.set id v1 e1) (PTree.set id v2 e2).
Proof.
  intros; red; intros. rewrite PTree.gsspec in *. destruct (peq id0 id).
  exists v2; split; congruence.
  auto.
Qed.

Lemma set_params_lessdef:
  forall il vl1 vl2, 
  Val.lessdef_list vl1 vl2 ->
  env_lessdef (set_params vl1 il) (set_params vl2 il).
Proof.
  induction il; simpl; intros.
  red; intros. rewrite PTree.gempty in H0; congruence.
  inv H; apply set_var_lessdef; auto.
Qed.

Lemma set_locals_lessdef:
  forall e1 e2, env_lessdef e1 e2 ->
  forall il, env_lessdef (set_locals il e1) (set_locals il e2).
Proof.
  induction il; simpl. auto. apply set_var_lessdef; auto.
Qed.

(** Semantic preservation for expressions. *)

Lemma sel_expr_correct:
  forall sp e m a v,
  Cminor.eval_expr ge sp e m a v ->
  forall e' le m',
  env_lessdef e e' -> Mem.extends m m' ->
  exists v', eval_expr tge sp e' m' le (sel_expr a) v' /\ Val.lessdef v v'.
Proof.
  induction 1; intros; simpl.
  (* Evar *)
  exploit H0; eauto. intros [v' [A B]]. exists v'; split; auto. constructor; auto.
  (* Econst *)
  destruct cst; simpl in *; inv H. 
  exists (Vint i); split; auto. econstructor. constructor. auto. 
  exists (Vfloat f); split; auto. econstructor. constructor. auto.
  exists (Vsingle f); split; auto. econstructor. constructor. auto. 
  exists (Val.longofwords (Vint (Int64.hiword i)) (Vint (Int64.loword i))); split.
  eapply eval_Eop. constructor. EvalOp. simpl; eauto. constructor. EvalOp. simpl; eauto. constructor. auto.
  simpl. rewrite Int64.ofwords_recompose. auto.
  rewrite <- symbols_preserved. fold (Genv.symbol_address tge i i0). apply eval_addrsymbol.
  apply eval_addrstack.
  (* Eunop *)
  exploit IHeval_expr; eauto. intros [v1' [A B]].
  exploit eval_unop_lessdef; eauto. intros [v' [C D]].
  exploit eval_sel_unop; eauto. intros [v'' [E F]].
  exists v''; split; eauto. eapply Val.lessdef_trans; eauto. 
  (* Ebinop *)
  exploit IHeval_expr1; eauto. intros [v1' [A B]].
  exploit IHeval_expr2; eauto. intros [v2' [C D]].
  exploit eval_binop_lessdef; eauto. intros [v' [E F]].
  exploit eval_sel_binop. eexact A. eexact C. eauto. intros [v'' [P Q]].
  exists v''; split; eauto. eapply Val.lessdef_trans; eauto. 
  (* Eload *)
  exploit IHeval_expr; eauto. intros [vaddr' [A B]].
  exploit Mem.loadv_extends; eauto. intros [v' [C D]].
  exists v'; split; auto. eapply eval_load; eauto.
Qed.

Lemma sel_exprlist_correct:
  forall sp e m a v,
  Cminor.eval_exprlist ge sp e m a v ->
  forall e' le m',
  env_lessdef e e' -> Mem.extends m m' ->
  exists v', eval_exprlist tge sp e' m' le (sel_exprlist a) v' /\ Val.lessdef_list v v'.
Proof.
  induction 1; intros; simpl. 
  exists (@nil val); split; auto. constructor.
  exploit sel_expr_correct; eauto. intros [v1' [A B]].
  exploit IHeval_exprlist; eauto. intros [vl' [C D]].
  exists (v1' :: vl'); split; auto. constructor; eauto.
Qed.

(** Semantic preservation for functions and statements. *)

Inductive match_cont: Cminor.cont -> CminorSel.cont -> Prop :=
  | match_cont_stop:
      match_cont Cminor.Kstop Kstop
  | match_cont_seq: forall s s' k k' sprog,
      sel_stmt (Genv.globalenv sprog) s = OK s' ->
      forall (SPROG: program_linkeq Language_Cminor sprog prog),
      match_cont k k' ->
      match_cont (Cminor.Kseq s k) (Kseq s' k')
  | match_cont_block: forall k k',
      match_cont k k' ->
      match_cont (Cminor.Kblock k) (Kblock k')
  | match_cont_call: forall id f sp e k f' e' k' sprog,
      sel_function (Genv.globalenv sprog) f = OK f' ->
      forall (SPROG: program_linkeq Language_Cminor sprog prog),
      match_cont k k' -> env_lessdef e e' ->
      match_cont (Cminor.Kcall id f sp e k) (Kcall id f' sp e' k').

Inductive match_states: Cminor.state -> CminorSel.state -> Prop :=
  | match_state: forall f f' s k s' k' sp e m e' m' sprog1 sprog2
        (TF: sel_function (Genv.globalenv sprog1) f = OK f')
        (TS: sel_stmt (Genv.globalenv sprog2) s = OK s')
        (SPROG1: program_linkeq Language_Cminor sprog1 prog)
        (SPROG2: program_linkeq Language_Cminor sprog2 prog)
        (MC: match_cont k k')
        (LD: env_lessdef e e')
        (ME: Mem.extends m m'),
      match_states
        (Cminor.State f s k sp e m)
        (State f' s' k' sp e' m')
  | match_callstate: forall f f' args args' k k' m m' sprog
        (TF: sel_fundef (Genv.globalenv sprog) f = OK f')
        (SPROG: program_linkeq Language_Cminor sprog prog)
        (MC: match_cont k k')
        (LD: Val.lessdef_list args args')
        (ME: Mem.extends m m'),
      match_states
        (Cminor.Callstate f args k m)
        (Callstate f' args' k' m')
  | match_returnstate: forall v v' k k' m m'
        (MC: match_cont k k')
        (LD: Val.lessdef v v')
        (ME: Mem.extends m m'),
      match_states
        (Cminor.Returnstate v k m)
        (Returnstate v' k' m')
  | match_builtin_1: forall ef args args' optid f sp e k m al f' e' k' m' sprog
        (TF: sel_function (Genv.globalenv sprog) f = OK f')
        (SPROG: program_linkeq Language_Cminor sprog prog)
        (MC: match_cont k k')
        (LDA: Val.lessdef_list args args')
        (LDE: env_lessdef e e')
        (ME: Mem.extends m m')
        (EA: eval_exprlist tge sp e' m' nil al args'),
      match_states
        (Cminor.Callstate (External ef) args (Cminor.Kcall optid f sp e k) m)
        (State f' (Sbuiltin optid ef al) k' sp e' m')
  | match_builtin_2: forall v v' optid f sp e k m f' e' m' k' sprog
        (TF: sel_function (Genv.globalenv sprog) f = OK f')
        (SPROG: program_linkeq Language_Cminor sprog prog)
        (MC: match_cont k k')
        (LDV: Val.lessdef v v')
        (LDE: env_lessdef e e')
        (ME: Mem.extends m m'),
      match_states
        (Cminor.Returnstate v (Cminor.Kcall optid f sp e k) m)
        (State f' Sskip k' sp (set_optvar optid v' e') m').

Remark call_cont_commut:
  forall k k', match_cont k k' -> match_cont (Cminor.call_cont k) (call_cont k').
Proof.
  induction 1; simpl; auto. constructor. econstructor; eauto.
Qed.

Remark find_label_commut:
  forall lbl s k s' k' sprog,
  match_cont k k' ->
  sel_stmt (Genv.globalenv sprog) s = OK s' ->
  forall (SPROG: program_linkeq Language_Cminor sprog prog),
  match Cminor.find_label lbl s k, find_label lbl s' k' with
  | None, None => True
  | Some(s1, k1), Some(s1', k1') => sel_stmt (Genv.globalenv sprog) s1 = OK s1' /\ match_cont k1 k1'
  | _, _ => False
  end.
Proof.
  induction s; intros until sprog; simpl; intros MC SE SPROG; try (monadInv SE); simpl; auto.
(* store *)
  unfold store. destruct (addressing m (sel_expr e)); simpl; auto.
(* call *)
  destruct (classify_call (Genv.globalenv sprog) e); simpl; auto.
(* tailcall *)
  destruct (classify_call (Genv.globalenv sprog) e); simpl; auto.
(* seq *)
  exploit (IHs1 (Cminor.Kseq s2 k)); eauto. econstructor; eauto.  
  destruct (Cminor.find_label lbl s1 (Cminor.Kseq s2 k)) as [[sx kx] | ];
  destruct (find_label lbl x (Kseq x0 k')) as [[sy ky] | ];
  intuition. eapply IHs2; eauto.
(* ifthenelse *)
  exploit (IHs1 k); eauto. 
  destruct (Cminor.find_label lbl s1 k) as [[sx kx] | ];
  destruct (find_label lbl x k') as [[sy ky] | ];
  intuition. eapply IHs2; eauto.
(* loop *)
  eapply IHs; eauto. econstructor; eauto. simpl; rewrite EQ; auto.
(* block *)
  eapply IHs; eauto. constructor; auto.
(* switch *)
  destruct b. 
  destruct (validate_switch Int64.modulus n l (compile_switch Int64.modulus n l)); inv SE.
  simpl; auto.
  destruct (validate_switch Int.modulus n l (compile_switch Int.modulus n l)); inv SE.
  simpl; auto.
(* return *)
  destruct o; inv SE; simpl; auto.
(* label *)
  destruct (ident_eq lbl l). auto. apply IHs; auto.
Qed.

Definition measure (s: Cminor.state) : nat :=
  match s with
  | Cminor.Callstate _ _ _ _ => 0%nat
  | Cminor.State _ _ _ _ _ _ => 1%nat
  | Cminor.Returnstate _ _ _ => 2%nat
  end.

Lemma sel_step_correct:
  forall S1 t S2, Cminor.step ge S1 t S2 ->
  forall T1, match_states S1 T1 ->
  (exists T2, step tge T1 t T2 /\ match_states S2 T2)
  \/ (measure S2 < measure S1 /\ t = E0 /\ match_states S2 T1)%nat.
Proof.
  induction 1; intros T1 ME; inv ME; try (monadInv TS).
- (* skip seq *)
  inv MC. left; econstructor; split. econstructor. econstructor; eauto.
- (* skip block *)
  inv MC. left; econstructor; split. econstructor. econstructor; eauto.
- (* skip call *)
  exploit Mem.free_parallel_extends; eauto. intros [m2' [A B]].
  left; econstructor; split. 
  econstructor. inv MC; simpl in H; simpl; auto. 
  eauto. 
  erewrite stackspace_function_translated; eauto. 
  constructor; auto.
- (* assign *)
  exploit sel_expr_correct; eauto. intros [v' [A B]].
  unfold sel_function in TF.
  left; econstructor; split.
  econstructor; eauto.
  econstructor; eauto. apply set_var_lessdef; auto.
- (* store *)
  exploit sel_expr_correct. eexact H. eauto. eauto. intros [vaddr' [A B]].
  exploit sel_expr_correct. eexact H0. eauto. eauto. intros [v' [C D]].
  exploit Mem.storev_extends; eauto. intros [m2' [P Q]].
  left; econstructor; split.
  eapply eval_store; eauto.
  econstructor; eauto.
- (* Scall *)
  exploit sel_exprlist_correct; eauto. intros [vargs' [C D]].
  exploit classify_call_correct_ext; eauto. 
  simpl. fold Cminor.fundef.
  destruct (classify_call (Genv.globalenv sprog2) a) as [ | id | ef].
+ (* indirect *)
  exploit sel_expr_correct; eauto. intros [vf' [A B]].
  exploit functions_translated; eauto. intros (fd' & U & sprog' & SPROG' & V).
  left; econstructor; split.
  econstructor; eauto. econstructor; eauto. 
  eapply sig_function_translated; eauto.
  econstructor; eauto. econstructor; eauto.
+ (* direct *)
  intros [b [U V]]. 
  exploit functions_translated; eauto. intros (fd' & X & sprog' & SPROG' & Y).
  left; econstructor; split.
  econstructor; eauto.
  subst vf. econstructor; eauto. rewrite symbols_preserved; eauto.
  eapply sig_function_translated; eauto.
  econstructor; eauto. econstructor; eauto.
+ (* turned into Sbuiltin *)
  intros EQ. subst fd. 
  right; split. simpl. omega. split. auto. 
  econstructor; eauto.
- (* Stailcall *)
  exploit Mem.free_parallel_extends; eauto. intros [m2' [P Q]].
  erewrite <- stackspace_function_translated in P by eauto.
  exploit sel_expr_correct; eauto. intros [vf' [A B]].
  exploit sel_exprlist_correct; eauto. intros [vargs' [C D]].
  exploit functions_translated; eauto. intros [fd' [E [sprog' [SPROG' F]]]].
  left; econstructor; split.
  exploit classify_call_correct_ext; try apply SPROG2; eauto. 
  simpl in *. fold Cminor.fundef in *.
  destruct (classify_call (Genv.globalenv sprog2) a) as [ | id | ef]; intros. 
  econstructor; eauto. econstructor; eauto. eapply sig_function_translated; eauto.
  destruct H2 as [b [U V]]. subst vf. inv B. 
  econstructor; eauto. econstructor; eauto. rewrite symbols_preserved; eauto. eapply sig_function_translated; eauto.
  econstructor; eauto. econstructor; eauto. eapply sig_function_translated; eauto.
  econstructor; eauto. apply call_cont_commut; auto.
- (* Sbuiltin *)
  exploit sel_exprlist_correct; eauto. intros [vargs' [P Q]].
  exploit external_call_mem_extends; eauto. 
  intros [vres' [m2 [A [B [C D]]]]].
  left; econstructor; split.
  econstructor. eauto. eapply external_call_symbols_preserved; eauto.
  exact symbols_preserved. exact varinfo_preserved.
  econstructor; eauto.
  destruct optid; simpl; auto. apply set_var_lessdef; auto.
- (* Seq *)
  left; econstructor; split.
  constructor. econstructor; eauto. econstructor; eauto.
- (* Sifthenelse *)
  exploit sel_expr_correct; eauto. intros [v' [A B]].
  assert (Val.bool_of_val v' b). inv B. auto. inv H0.
  left; exists (State f' (if b then x else x0) k' sp e' m'); split.
  econstructor; eauto. eapply eval_condexpr_of_expr; eauto. 
  econstructor; eauto. destruct b; auto.
- (* Sloop *)
  left; econstructor; split. constructor. econstructor; eauto.
  econstructor; eauto. simpl; rewrite EQ; auto.
- (* Sblock *)
  left; econstructor; split. constructor. econstructor; eauto. constructor; auto.
- (* Sexit seq *)
  inv MC. left; econstructor; split. constructor. econstructor; eauto.
- (* Sexit0 block *)
  inv MC. left; econstructor; split. constructor. econstructor; eauto.
- (* SexitS block *)
  inv MC. left; econstructor; split. constructor. econstructor; eauto.
- (* Sswitch *)
  inv H0; simpl in TS.
+ set (ct := compile_switch Int.modulus default cases) in *.
  destruct (validate_switch Int.modulus default cases ct) eqn:VALID; inv TS.
  exploit sel_expr_correct; eauto. intros [v' [A B]]. inv B.
  left; econstructor; split. 
  econstructor. eapply sel_switch_int_correct; eauto. 
  econstructor; eauto.
+ set (ct := compile_switch Int64.modulus default cases) in *.
  destruct (validate_switch Int64.modulus default cases ct) eqn:VALID; inv TS.
  exploit sel_expr_correct; eauto. intros [v' [A B]]. inv B.
  left; econstructor; split.
  econstructor. eapply sel_switch_long_correct; eauto.
  econstructor; eauto.
- (* Sreturn None *)
  exploit Mem.free_parallel_extends; eauto. intros [m2' [P Q]].
  erewrite <- stackspace_function_translated in P by eauto.
  left; econstructor; split. 
  econstructor. simpl; eauto. 
  constructor; auto. apply call_cont_commut; auto.
- (* Sreturn Some *)
  exploit Mem.free_parallel_extends; eauto. intros [m2' [P Q]].
  erewrite <- stackspace_function_translated in P by eauto.
  exploit sel_expr_correct; eauto. intros [v' [A B]].
  left; econstructor; split. 
  econstructor; eauto.
  constructor; auto. apply call_cont_commut; auto.
- (* Slabel *)
  left; econstructor; split. constructor. econstructor; eauto.
- (* Sgoto *)
  assert (sel_stmt (Genv.globalenv sprog1) (Cminor.fn_body f) = OK (fn_body f')).
  { monadInv TF; simpl; auto. }
  exploit (find_label_commut lbl (Cminor.fn_body f) (Cminor.call_cont k)).
    apply call_cont_commut; eauto. eauto. auto. auto.
  rewrite H. 
  destruct (find_label lbl (fn_body f') (call_cont k'0))
  as [[s'' k'']|] eqn:?; intros; try contradiction.
  destruct H1. 
  left; econstructor; split.
  econstructor; eauto. 
  econstructor; eauto.
- (* internal function *)
  monadInv TF. generalize EQ; intros TF; monadInv TF.
  exploit Mem.alloc_extends. eauto. eauto. apply Zle_refl. apply Zle_refl. 
  intros [m2' [A B]].
  left; econstructor; split.
  econstructor; simpl; eauto.
  econstructor; simpl; eauto. apply set_locals_lessdef. apply set_params_lessdef; auto.
- (* external call *)
  monadInv TF.
  exploit external_call_mem_extends; eauto. 
  intros [vres' [m2 [A [B [C D]]]]].
  left; econstructor; split.
  econstructor. eapply external_call_symbols_preserved; eauto.
  exact symbols_preserved. exact varinfo_preserved.
  constructor; auto.
- (* external call turned into a Sbuiltin *)
  exploit external_call_mem_extends; eauto. 
  intros [vres' [m2 [A [B [C D]]]]].
  left; econstructor; split.
  econstructor. eauto. eapply external_call_symbols_preserved; eauto.
  exact symbols_preserved. exact varinfo_preserved.
  econstructor; eauto.
- (* return *)
  inv MC. 
  left; econstructor; split. 
  econstructor. 
  econstructor; eauto. destruct optid; simpl; auto. apply set_var_lessdef; auto.
- (* return of an external call turned into a Sbuiltin *)
  right; split. simpl; omega. split. auto. econstructor; eauto. 
  destruct optid; simpl; auto. apply set_var_lessdef; auto.
Qed.

Lemma sel_initial_states:
  forall S, Cminor.initial_state prog S ->
  exists R, initial_state tprog R /\ match_states S R.
Proof.
  induction 1.
  exploit function_ptr_translated; eauto. intros (f' & A & sprog & SPROG & B).
  econstructor; split.
  econstructor.
  exploit Genv.init_mem_match; eauto.
  replace (prog_main tprog) with (prog_main prog).
  rewrite symbols_preserved. eauto.
  inv TRANSF. auto.
  exploit function_ptr_translated; eauto.
  rewrite <- H2. eapply sig_function_translated; eauto.
  econstructor; eauto. constructor. apply Mem.extends_refl.
Qed.

Lemma sel_final_states:
  forall S R r,
  match_states S R -> Cminor.final_state S r -> final_state R r.
Proof.
  intros. inv H0. inv H. inv MC. inv LD. constructor.
Qed.

Theorem transl_program_correct:
  forward_simulation (Cminor.semantics prog) (CminorSel.semantics tprog).
Proof.
  apply forward_simulation_opt with (match_states := match_states) (measure := measure). 
  eapply symbols_preserved; eauto.
  apply sel_initial_states; auto.
  apply sel_final_states; auto.
  apply sel_step_correct; auto.
Qed.

End PRESERVATION.

Lemma check_helper_correct:
  forall ge name sg res,
  check_helper ge (name, sg) = OK res -> helper_declared ge name sg.
Proof with (try discriminate).
  unfold check_helper; intros. 
  destruct (Genv.find_symbol ge name) as [b|] eqn:FS...
  destruct (Genv.find_funct_ptr ge b) as [fd|] eqn:FP...
  destruct fd... destruct e... destruct (ident_eq name0 name)... 
  destruct (signature_eq sg0 sg)... 
  subst. exists b; auto.
Qed.

Lemma check_helpers_correct:
  forall ge res, check_helpers ge = OK res ->
  forall name sg, In (name, sg) i64_helpers -> helper_declared ge name sg.
Proof.
  unfold check_helpers; intros ge res CH name sg. 
  monadInv CH. generalize (mmap_inversion _ _ EQ). 
  generalize i64_helpers x. induction 1; simpl; intros.
  contradiction.
  destruct H1. subst a1. eapply check_helper_correct; eauto. eauto. 
Qed.

Lemma link_program_check_helper
      idsig p1 p2 p
      (LINK: link_program Language_Cminor p1 p2 = Some p)
      (CHECK1: SelectLong.check_helper (Genv.globalenv p1) idsig = OK tt)
      (CHECK2: SelectLong.check_helper (Genv.globalenv p2) idsig = OK tt):
  SelectLong.check_helper (Genv.globalenv p) idsig = OK tt.
Proof.
  destruct idsig as [id sig]. simpl in *.
  destruct (@Genv.find_symbol Cminor.fundef unit (Genv.globalenv p1) id) as [s1|] eqn:SYM1; try congruence.
  destruct (@Genv.find_symbol Cminor.fundef unit (Genv.globalenv p2) id) as [s2|] eqn:SYM2; try congruence.
  destruct (@Genv.find_funct_ptr Cminor.fundef unit (Genv.globalenv p1) s1) as [f1|] eqn:FUNC1; try congruence.
  destruct (@Genv.find_funct_ptr Cminor.fundef unit (Genv.globalenv p2) s2) as [f2|] eqn:FUNC2; try congruence.
  destruct f1 as [|[]]; try congruence.
  destruct f2 as [|[]]; try congruence.
  destruct (ident_eq name id); simpl in *; subst; try congruence.
  destruct (signature_eq sg sig); simpl in *; subst; try congruence.
  destruct (ident_eq name0 id); simpl in *; subst; try congruence.
  destruct (signature_eq sg0 sig); simpl in *; subst; try congruence.
  exploit find_symbol_spec; eauto.
  instantiate (1 := p1). instantiate (1 := id).
  simpl in *. fold Cminor.fundef in *. rewrite SYM1, FUNC1.
  intro ID1.
  exploit find_symbol_spec; eauto.
  instantiate (1 := p2). instantiate (1 := id).
  simpl in *. fold Cminor.fundef in *. rewrite SYM2, FUNC2.
  intro ID2.
  exploit find_symbol_spec; eauto.
  instantiate (1 := p). instantiate (1 := id).
  simpl in *. fold Cminor.fundef in *.
  intro ID.
  unfold link_program in LINK. simpl in *. fold Cminor.fundef in *.
  destruct (Pos.eqb (prog_main p1) (prog_main p2)); try congruence.
  destruct (link_globdef_list Language_Cminor (prog_defs p1) (prog_defs p2)) eqn:DEFS; inv LINK.
  unfold link_globdef_list in DEFS. simpl in *. fold Cminor.fundef in *.
  destruct (link_globdefs Language_Cminor (PTree_unelements (prog_defs p1)) (PTree_unelements (prog_defs p2))) eqn:DEFS'; inv DEFS.
  exploit gtlink_globdefs; eauto. instantiate (1 := id). rewrite ? PTree_guespec.
  revert ID1 ID2. simpl in *. fold Cminor.fundef in *. fold ident.
  destruct
    (@option_map (prod ident (globdef Cminor.fundef unit))
                 (globdef Cminor.fundef unit) (@snd ident (globdef Cminor.fundef unit))
                 (@find (prod ident (globdef Cminor.fundef unit))
                        (fun id0 : prod ident (globdef Cminor.fundef unit) =>
                           @proj_sumbool
                             (@eq ident id (@fst ident (globdef Cminor.fundef unit) id0))
                             (not
                                (@eq ident id (@fst ident (globdef Cminor.fundef unit) id0)))
                             (peq id (@fst ident (globdef Cminor.fundef unit) id0)))
                        (@rev (prod ident (globdef Cminor.fundef unit))
                              (@prog_defs Cminor.fundef unit p1)))); [|intros; exfalso; auto].
  destruct
    (@option_map (prod ident (globdef Cminor.fundef unit))
                 (globdef Cminor.fundef unit) (@snd ident (globdef Cminor.fundef unit))
                 (@find (prod ident (globdef Cminor.fundef unit))
                        (fun id0 : prod ident (globdef Cminor.fundef unit) =>
                           @proj_sumbool
                             (@eq ident id (@fst ident (globdef Cminor.fundef unit) id0))
                             (not
                                (@eq ident id (@fst ident (globdef Cminor.fundef unit) id0)))
                             (peq id (@fst ident (globdef Cminor.fundef unit) id0)))
                        (@rev (prod ident (globdef Cminor.fundef unit))
                              (@prog_defs Cminor.fundef unit p2)))); [|intros; exfalso; auto].
  destruct g, g0; intros; try (exfalso; auto; fail).
  destruct (t ! id) eqn:TID; [|exfalso; auto].
  rewrite PTree_gespec in TID.
  rewrite <- list_norepet_option_map_find in TID; [|apply PTree.elements_keys_norepet].
  simpl in *. fold Cminor.fundef ident in *. rewrite TID in ID.
  destruct (Genv.find_symbol (Genv.globalenv {| prog_defs := PTree.elements t; prog_main := prog_main p1 |}) id); [|exfalso; auto].
  destruct g; [|destruct H as [[]|[]]; congruence].
  destruct (Genv.find_funct_ptr (Genv.globalenv {| prog_defs := PTree.elements t; prog_main := prog_main p1 |}) b); [|exfalso; auto].
  destruct (Genv.find_var_info (Genv.globalenv {| prog_defs := PTree.elements t; prog_main := prog_main p1 |}) b); [exfalso; auto|].
  destruct (Genv.find_var_info (Genv.globalenv p1) s1); [exfalso; auto|].
  destruct (Genv.find_var_info (Genv.globalenv p2) s2); [exfalso; auto|].
  subst. destruct H as [[]|[]]; inv H0.
  - destruct (ident_eq id id); [|congruence].
    destruct (signature_eq sig sig); [|congruence].
    auto.
  - destruct (ident_eq id id); [|congruence].
    destruct (signature_eq sig sig); [|congruence].
    auto.
Qed.

Lemma link_program_check_helpers
      p1 p2 p
      (LINK: link_program Language_Cminor p1 p2 = Some p)
      (CHECK1: SelectLong.check_helpers (Genv.globalenv p1) = OK tt)
      (CHECK2: SelectLong.check_helpers (Genv.globalenv p2) = OK tt):
  SelectLong.check_helpers (Genv.globalenv p) = OK tt.
Proof.
  unfold SelectLong.check_helpers in *.
  monadInv CHECK1. monadInv CHECK2.
  apply mmap_inversion in EQ. apply mmap_inversion in EQ0.
  revert x x0 EQ EQ0. induction SelectLong.i64_helpers; intros; auto.
  inv EQ. inv EQ0. destruct b0, b1. simpl.
  erewrite link_program_check_helper; eauto. simpl.
  exploit IHl; eauto. simpl in *.
  destruct (mmap (SelectLong.check_helper (Genv.globalenv p)) l); auto.
Qed.

Lemma Selection_sepcomp_rel
      cminorprog cminorselprog
      (Htrans: Selection.sel_program cminorprog = OK cminorselprog):
  @sepcomp_rel
    Language.Language_Cminor Language.Language_CminorSel
    (fun p f tf => Selection.sel_function (Genv.globalenv p) f = OK tf)
    (fun p ef tef => ef = tef)
    (@OK _)
    cminorprog cminorselprog.
Proof.
  monadInv Htrans.
  destruct cminorprog as [defs ?], cminorselprog as [tdefs ?].
  unfold transform_partial_program, transform_partial_program2 in EQ0. monadInv EQ0.
  constructor; auto. simpl in *.
  revert tdefs EQ EQ1. generalize defs at 1 2 4 as fdefs.
  induction defs; simpl; intros fdefs tdefs Hhelpers Hdefs.
  { inv Hdefs. constructor. }
  destruct a. destruct g.
  - match goal with
      | [H: match ?x with OK _ => _ | Error _ => _ end = OK _ |- _] =>
        destruct x as [tf|] eqn:Hf; [|inv H]
    end.
    monadInv Hdefs. constructor; simpl.
    + split; auto. eexists. split; [reflexivity|].
      destruct f; inv Hf.
      * monadInv H0.
        eapply (@grel_f Language.Language_Cminor Language.Language_CminorSel); simpl; auto.
      * eapply (@grel_ef Language.Language_Cminor Language.Language_CminorSel); simpl; auto.
    + apply IHdefs; auto.
  - monadInv Hdefs. constructor; simpl.
    + split; auto. eexists. split; [reflexivity|].
      eapply (@grel_gv Language.Language_Cminor Language.Language_CminorSel); auto.
    + apply IHdefs; auto.
Qed.
