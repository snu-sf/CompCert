Require Import RelationClasses.
Require String.
Require Import Coqlib Coqlib_linker.
Require Import Maps Maps_linker.
Require Import Integers Floats Values AST Globalenvs.
Require Import Language Linker LinkerProp Linkeq.
Require Import Errors.

Set Implicit Arguments.

Section SEPCOMP_RELATION.

Variable (lang_src lang_tgt:Language).
Variable grel:
  forall (prog_src:lang_src.(progT))
         (g_src:lang_src.(globdefT))
         (g_tgt:lang_tgt.(globdefT)), Prop.

Section DEF.

Variable (prog_src:lang_src.(progT)).
Variable (prog_tgt:lang_tgt.(progT)).

Inductive program_rel: Prop :=
| program_rel_intro
    (Hmain: prog_src.(prog_main) = prog_tgt.(prog_main))
    (Hdefs:
       list_forall2
         (fun g_src g_tgt =>
            fst g_src = fst g_tgt /\
            exists p,
              program_linkeq lang_src p prog_src /\
              grel p (snd g_src) (snd g_tgt))
         prog_src.(prog_defs) prog_tgt.(prog_defs))
.

End DEF.

(** properties of linking on separate compilation relation *)

Lemma link_program_rel
      (prog1_src prog2_src prog_src:lang_src.(progT))
      (prog1_tgt prog2_tgt:lang_tgt.(progT))
      (Hprog_src: link_program lang_src prog1_src prog2_src = Some prog_src)
      (Hprog1: program_rel prog1_src prog1_tgt)
      (Hprog2: program_rel prog2_src prog2_tgt):
  exists prog_tgt,
    link_program lang_tgt prog1_tgt prog2_tgt = Some prog_tgt /\
    program_rel prog_src prog_tgt.
Proof.
  destruct prog1_src as [def1_src ?],
           prog2_src as [def2_src ?],
           prog_src as [def_src ?],
           prog1_tgt as [def1_tgt ?],
           prog2_tgt as [def2_tgt ?].
  unfold link_program in *. simpl in *.
  inv Hprog1. inv Hprog2. simpl in *. subst.
  destruct (prog_main2 =? prog_main3)%positive eqn:Hmain; [|inv Hprog_src; fail].
  apply Peqb_true_eq in Hmain. subst.
  destruct (link_globdef_list lang_src def1_src def2_src) eqn:Hdef_src; inv Hprog_src.
  admit.
Qed.

End SEPCOMP_RELATION.

Section TRANSF_PARTIAL2.

Variable (sigT_src:Sig).
Variable (sigT_tgt:Sig).
Variable (fT_src:F sigT_src).
Variable (fT_tgt:F sigT_tgt).
Variable (efT_src:EF sigT_src).
Variable (efT_tgt:EF sigT_tgt).
Variable (fundefT_src:Fundef fT_src efT_src).
Variable (fundefT_tgt:Fundef fT_tgt efT_tgt).
Variable (vT_src:V).
Variable (vT_tgt:V).

Let lang_src := mkLanguage fundefT_src vT_src.
Let lang_tgt := mkLanguage fundefT_tgt vT_tgt.

Variable transf_fun: lang_src.(progT) -> fundefT_src -> res fundefT_tgt.
Variable transf_var: vT_src -> res vT_tgt.
Variable p: lang_src.(progT).
Variable p': lang_tgt.(progT).

Inductive match_globdef_transf_partial2 (prog_src:lang_src.(progT)):
  forall (def_src:lang_src.(globdefT))
         (def_tgt:lang_tgt.(globdefT)), Prop :=
| match_globdef_transf_partial2_fun
    fun_src fun_tgt
    (Hfun: transf_fun prog_src fun_src = OK fun_tgt):
    match_globdef_transf_partial2 prog_src (Gfun fun_src) (Gfun fun_tgt)
| match_globdef_transf_partial2_var
    var_src var_tgt
    (Hvar: transf_globvar transf_var var_src = OK var_tgt):
    match_globdef_transf_partial2 prog_src (Gvar var_src) (Gvar var_tgt)
.

Hypothesis Hprogram_rel: program_rel match_globdef_transf_partial2 p p'.

Lemma prog_match:
  match_program
    (fun fd tfd =>
       exists prog_src,
         program_linkeq lang_src prog_src p /\
         transf_fun prog_src fd = OK tfd)
    (fun info tinfo =>
       transf_var info = OK tinfo)
    nil p.(prog_main)
    p p'.
Proof.
  destruct p as [defs ?], p' as [defs' ?].
  inv Hprogram_rel. simpl in *. subst.
  revert defs' Hdefs. generalize defs at 1 3 as fdefs.
  induction defs; intros fdefs defs' Hdefs.
  { inv Hdefs. constructor; auto. exists nil. split; auto. constructor. }
  inv Hdefs. destruct a, b1, H1 as [? H1]. simpl in *. subst.
  eapply IHdefs in H3. destruct H3 as [H3 ?]. split; [|auto].
  destruct H3 as [? H3]. simpl in *. rewrite app_nil_r in *.
  destruct H3 as [H3 ?]. subst.
  eexists. rewrite app_nil_r. split; auto.
  constructor; auto.
  destruct H1 as [prog_src [Hprog_src H1]]. inv H1.
  - apply match_glob_fun. eexists. split; eauto.
  - monadInv Hvar. destruct var_src. simpl in *.
    apply match_glob_var. auto.
Qed.

Theorem find_funct_ptr_transf_partial2:
  forall (b: block) (f: fundefT_src),
  Genv.find_funct_ptr (Genv.globalenv p) b = Some f ->
  exists f',
  Genv.find_funct_ptr (Genv.globalenv p') b = Some f' /\ 
  exists prog_src,
    program_linkeq lang_src prog_src p /\
    transf_fun prog_src f = OK f'.
Proof.
  intros. 
  exploit Genv.find_funct_ptr_match. eexact prog_match. eauto. 
  intros [tf [X Y]]. exists tf; auto.
Qed.

Theorem find_funct_ptr_rev_transf_partial2:
  forall (b: block) (tf: fundefT_tgt),
  Genv.find_funct_ptr (Genv.globalenv p') b = Some tf ->
  exists f, Genv.find_funct_ptr (Genv.globalenv p) b = Some f /\ 
  exists prog_src,
    program_linkeq lang_src prog_src p /\
    transf_fun prog_src f = OK tf.
Proof.
  intros. 
  exploit Genv.find_funct_ptr_rev_match. eexact prog_match. eauto. 
  destruct (plt b (Genv.genv_next (Genv.globalenv p))); [|intro X; inv X].
  intros [f [X Y]]. exists f; auto.
Qed.

Theorem find_funct_transf_partial2:
  forall (v: val) (f: fundefT_src),
  Genv.find_funct (Genv.globalenv p) v = Some f ->
  exists f',
  Genv.find_funct (Genv.globalenv p') v = Some f' /\ 
  exists prog_src,
    program_linkeq lang_src prog_src p /\
    transf_fun prog_src f = OK f'.
Proof.
  intros. 
  exploit Genv.find_funct_match. eexact prog_match. eauto. 
  intros [tf [X Y]]. exists tf; auto.
Qed.

Theorem find_funct_rev_transf_partial2:
  forall (v: val) (tf: fundefT_tgt),
  Genv.find_funct (Genv.globalenv p') v = Some tf ->
  exists f, Genv.find_funct (Genv.globalenv p) v = Some f /\ 
  exists prog_src,
    program_linkeq lang_src prog_src p /\
    transf_fun prog_src f = OK tf.
Proof.
  intros. 
  exploit Genv.find_funct_rev_match. eexact prog_match. eauto. 
  intros [[f [X Y]]|X]; [|inv X]. exists f; auto.
Qed.

Theorem find_var_info_transf_partial2:
  forall (b: block) (v: globvar vT_src),
  Genv.find_var_info (Genv.globalenv p) b = Some v ->
  exists v',
  Genv.find_var_info (Genv.globalenv p') b = Some v' /\ transf_globvar transf_var v = OK v'.
Proof.
  intros. 
  exploit Genv.find_var_info_match. eexact prog_match. eauto. intros [tv [X Y]]. 
  exists tv; split; auto. inv Y. unfold transf_globvar; simpl.
  rewrite H0; simpl. auto.
Qed.

Theorem find_var_info_rev_transf_partial2:
  forall (b: block) (v': globvar vT_tgt),
  Genv.find_var_info (Genv.globalenv p') b = Some v' ->
  exists v,
  Genv.find_var_info (Genv.globalenv p) b = Some v /\ transf_globvar transf_var v = OK v'.
Proof.
  intros. 
  exploit Genv.find_var_info_rev_match. eexact prog_match. eauto.
  destruct (plt b (Genv.genv_next (Genv.globalenv p))); [|intro X; inv X].
  intros [v [X Y]]. exists v; split; auto. inv Y. unfold transf_globvar; simpl. 
  rewrite H0; simpl. auto.
Qed.

Theorem find_symbol_transf_partial2:
  forall (s: ident),
  Genv.find_symbol (Genv.globalenv p') s = Genv.find_symbol (Genv.globalenv p) s.
Proof.
  intros. eapply Genv.find_symbol_match. eexact prog_match. auto.
Qed.

Theorem init_mem_transf_partial2:
  forall m, Genv.init_mem p = Some m -> Genv.init_mem p' = Some m.
Proof.
  intros. erewrite Genv.init_mem_match; eauto.
  instantiate (1 := nil). eauto.
  eexact prog_match. auto.
Qed.

End TRANSF_PARTIAL2.

Section TRANSF_PROGRAM.

Variable (sigT_src:Sig).
Variable (sigT_tgt:Sig).
Variable (fT_src:F sigT_src).
Variable (fT_tgt:F sigT_tgt).
Variable (efT_src:EF sigT_src).
Variable (efT_tgt:EF sigT_tgt).
Variable (fundefT_src:Fundef fT_src efT_src).
Variable (fundefT_tgt:Fundef fT_tgt efT_tgt).
Variable (vT:V).

Let lang_src := mkLanguage fundefT_src vT.
Let lang_tgt := mkLanguage fundefT_tgt vT.

Variable transf: lang_src.(progT) -> fundefT_src -> fundefT_tgt.
Variable p: lang_src.(progT).
Variable tp: lang_tgt.(progT).

Inductive match_globdef_transf_program (prog_src:lang_src.(progT)):
  forall (def_src:lang_src.(globdefT))
         (def_tgt:lang_tgt.(globdefT)), Prop :=
| match_globdef_transf_program_fun
    fun_src fun_tgt
    (Hfun: transf prog_src fun_src = fun_tgt):
    match_globdef_transf_program prog_src (Gfun fun_src) (Gfun fun_tgt)
| match_globdef_transf_program_var var:
    match_globdef_transf_program prog_src (Gvar var) (Gvar var)
.

Hypothesis Hprogram_rel: program_rel match_globdef_transf_program p tp.

Remark transf_OK:
  program_rel (match_globdef_transf_partial2 (fun p x => OK (transf p x)) (fun v => OK v)) p tp.
Proof.
  inv Hprogram_rel. constructor; auto.
  eapply list_forall2_imply; eauto.
  simpl. intros. destruct v1, v2, H1 as [? X]. simpl in *. subst.
  destruct X as [prog_src [Hprog_src Hg]].
  split; auto. eexists. split; eauto.
  inv Hg.
  - constructor. auto.
  - constructor. destruct var. auto.
Qed.

Theorem find_funct_ptr_transf:
  forall (b: block) (f: fundefT_src),
  Genv.find_funct_ptr (Genv.globalenv p) b = Some f ->
  exists prog_src,
    program_linkeq lang_src prog_src p /\
    Genv.find_funct_ptr (Genv.globalenv tp) b = Some (transf prog_src f).
Proof.
  intros. 
  destruct (@find_funct_ptr_transf_partial2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ transf_OK _ _ H)
  as [f' [X [prog_src [Hprog_src Y]]]]. 
  simpl in *. eexists. split; eauto. congruence.
Qed.

Theorem find_funct_ptr_rev_transf:
  forall (b: block) (tf: fundefT_tgt),
  Genv.find_funct_ptr (Genv.globalenv tp) b = Some tf ->
  exists f, Genv.find_funct_ptr (Genv.globalenv p) b = Some f /\
            exists prog_src,
              program_linkeq lang_src prog_src p /\
              transf prog_src f = tf.
Proof.
  intros. exploit find_funct_ptr_rev_transf_partial2. eexact transf_OK. eauto.
  intros [f [X [prog_src [Hprog_src Y]]]]. exists f; split. auto. 
  eexists. split; eauto. congruence.
Qed.

Theorem find_funct_transf:
  forall (v: val) (f: fundefT_src),
  Genv.find_funct (Genv.globalenv p) v = Some f ->
  exists prog_src,
    program_linkeq lang_src prog_src p /\
    Genv.find_funct (Genv.globalenv tp) v = Some (transf prog_src f).
Proof.
  intros. 
  destruct (@find_funct_transf_partial2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ transf_OK _ _ H)
  as [f' [X [prog_src [Hprog_src Y]]]]. 
  eexists. split; eauto. simpl in *. congruence.
Qed.

Theorem find_funct_rev_transf:
  forall (v: val) (tf: fundefT_tgt),
  Genv.find_funct (Genv.globalenv tp) v = Some tf ->
  exists f, Genv.find_funct (Genv.globalenv p) v = Some f /\ 
            exists prog_src,
              program_linkeq lang_src prog_src p /\
              transf prog_src f = tf.
Proof.
  intros. exploit find_funct_rev_transf_partial2. eexact transf_OK. eauto.
  intros [f [X [prog_src [Hprog_src Y]]]]. exists f; split. auto. 
  eexists. split; eauto. congruence.
Qed.

Theorem find_symbol_transf:
  forall (s: ident),
  Genv.find_symbol (Genv.globalenv tp) s = Genv.find_symbol (Genv.globalenv p) s.
Proof.
  exact (@find_symbol_transf_partial2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ transf_OK).
Qed.

Theorem find_var_info_transf:
  forall (b: block),
  Genv.find_var_info (Genv.globalenv tp) b = Genv.find_var_info (Genv.globalenv p) b.
Proof.
  intros. destruct (Genv.find_var_info (Genv.globalenv p) b) as [v|] eqn:Hg.
  - exploit find_var_info_transf_partial2; try apply transf_OK; eauto.
    simpl. intros [v' [Hv' X]]. destruct v. inv X. auto.
  - destruct (Genv.find_var_info (Genv.globalenv tp) b) as [v|] eqn:Hg'; [|auto].
    exploit find_var_info_rev_transf_partial2; try apply transf_OK; eauto.
    simpl. intros [v' [Hv' X]].
    simpl in *. rewrite Hg in Hv'. inv Hv'.
Qed.

Theorem init_mem_transf:
  forall m, Genv.init_mem p = Some m -> Genv.init_mem tp = Some m.
Proof.
  exact (@init_mem_transf_partial2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ transf_OK).
Qed.

End TRANSF_PROGRAM.
