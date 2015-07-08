Require Import RelationClasses.
Require String.
Require Import Coqlib CoqlibExtra.
Require Import Maps MapsExtra.
Require Import Integers Floats Values AST Globalenvs.
Require Import Language Linker LinkerProp Linkeq.
Require Import Errors.
Require Import sflib paconotation.

Set Implicit Arguments.

Ltac clarify :=
  repeat
    match goal with
      | [H: False |- _] => inv H
      | [H1: ?x = _, H2: ?x = _ |- _] => rewrite H1 in H2; inv H2
    end.

Section SEPCOMP_RELATION.

Variable (lang_src lang_tgt:Language).

Variable transf_sigT: forall (ef:lang_src.(sigT)), lang_tgt.(sigT).
Variable frel:
  forall (prog_src:lang_src.(progT))
         (f_src:lang_src.(fT))
         (f_tgt:lang_tgt.(fT)), Prop.
Variable efrel:
  forall (prog_src:lang_src.(progT))
         (ef_src:lang_src.(efT))
         (ef_tgt:lang_tgt.(efT)), Prop.
Variable transf_vT: forall (v_src:lang_src.(vT)), res lang_tgt.(vT).

Hypothesis frel_sigT:
  forall p_src f_src f_tgt (H: frel p_src f_src f_tgt),
    transf_sigT (lang_src.(fT).(F_sig) f_src) = lang_tgt.(fT).(F_sig) f_tgt.
Hypothesis efrel_mon:
  forall p1 p2 ef tef
         (Hp: program_linkeq lang_src p1 p2)
         (Hef1: efrel p1 ef tef),
    efrel p2 ef tef.
Hypothesis efrel_fun:
  forall p ef tef1 tef2
         (Hef1: efrel p ef tef1)
         (Hef2: efrel p ef tef2),
    tef1 = tef2.
Hypothesis transf_efT_sigT:
  forall p_src ef_src ef_tgt (H: efrel p_src ef_src ef_tgt),
    transf_sigT (lang_src.(efT).(EF_sig) ef_src) = lang_tgt.(efT).(EF_sig) ef_tgt.
Hypothesis transf_efT_linkable:
  forall p_src ef_src ef_tgt (H: efrel p_src ef_src ef_tgt),
    lang_src.(efT).(EF_linkable) ef_src = lang_tgt.(efT).(EF_linkable) ef_tgt.

Inductive grel (prog_src:lang_src.(progT)):
  forall (g_src:lang_src.(globdefT))
         (g_tgt:lang_tgt.(globdefT)), Prop:=
| grel_f
    fd_src fd_tgt f_src f_tgt
    (Hf_src: lang_src.(fundefT).(Fundef_equiv).(AtoB) fd_src = inl f_src)
    (Hf_tgt: lang_tgt.(fundefT).(Fundef_equiv).(AtoB) fd_tgt = inl f_tgt)
    (Hf: frel prog_src f_src f_tgt):
    grel prog_src (Gfun fd_src) (Gfun fd_tgt)
| grel_ef
    fd_src fd_tgt ef_src ef_tgt
    (Hef_src: lang_src.(fundefT).(Fundef_equiv).(AtoB) fd_src = inr ef_src)
    (Hef_tgt: lang_tgt.(fundefT).(Fundef_equiv).(AtoB) fd_tgt = inr ef_tgt)
    (Hef: efrel prog_src ef_src ef_tgt):
    grel prog_src (Gfun fd_src) (Gfun fd_tgt)
| grel_gv
    gv_src gv_tgt
    (Hv: transf_globvar transf_vT gv_src = OK gv_tgt):
    grel prog_src (Gvar gv_src) (Gvar gv_tgt)
.

Lemma linkable_grel_linkable
      p1 g1 tg1 p2 g2 tg2 p
      (Hg: globdef_linkable lang_src g1 g2)
      (H1: grel p1 g1 tg1)
      (H2: grel p2 g2 tg2)
      (Hp1: program_linkeq lang_src p1 p)
      (Hp2: program_linkeq lang_src p2 p):
  globdef_linkable lang_tgt tg1 tg2.
Proof.
  inv H1; inv H2; inv Hg; inv Hv; clarify.
  - constructor. econstructor; eauto.
    + erewrite <- transf_efT_linkable; eauto.
    + erewrite <- transf_efT_sigT; eauto.
      erewrite <- frel_sigT; eauto.
      rewrite Hsig. auto.
  - constructor. eapply globfun_linkable_ee; eauto.
    rewrite Hef_tgt0. f_equal. eauto.
  - inv Hv0. inv Hv1. monadInv H0. monadInv H1.
    destruct gv_src, gv_src0. simpl in *. subst.
    rewrite EQ in EQ0. inv EQ0.
    constructor. constructor; auto.
Qed.

Inductive sepcomp_rel (prog_src:lang_src.(progT)) (prog_tgt:lang_tgt.(progT)): Prop :=
| sepcomp_rel_intro
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

(** properties of linking on separate compilation relation *)

Lemma link_program_sepcomp_rel
      (prog1_src prog2_src prog_src:lang_src.(progT))
      (prog1_tgt prog2_tgt:lang_tgt.(progT))
      (Hprog_src: link_program lang_src prog1_src prog2_src = Some prog_src)
      (Hprog1: sepcomp_rel prog1_src prog1_tgt)
      (Hprog2: sepcomp_rel prog2_src prog2_tgt):
  exists prog_tgt,
    link_program lang_tgt prog1_tgt prog2_tgt = Some prog_tgt /\
    sepcomp_rel prog_src prog_tgt.
Proof.
  exploit link_program_linkeq_l; eauto. intro Hle1.
  exploit link_program_linkeq_r; eauto. intro Hle2.
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
  apply (list_forall2_PTree_unelements
           (fun g1 g2 =>
              exists p,
                program_linkeq lang_src p {| prog_defs := def1_src; prog_main := prog_main1 |} /\
                grel p g1 g2)) in Hdefs.
  apply (list_forall2_PTree_unelements
           (fun g1 g2 =>
              exists p,
                program_linkeq lang_src p {| prog_defs := def2_src; prog_main := prog_main1 |} /\
                grel p g1 g2)) in Hdefs0.
  unfold link_globdef_list in *.
  revert Hdefs Hdefs0 Hdef_src.
  unfold globdefT. simpl.
  repeat match goal with
           | [|- context[@PTree_unelements ?T ?l]] => generalize (@PTree_unelements T l)
         end.
  intros def2'_tgt def2'_src def1'_tgt def1'_src H1 H2 Hsrc.
  match goal with
    | [H: context[match ?l with Some _ => _ | None => _ end] |- _] =>
      destruct l as [defs_src|] eqn:Hdefs_src; inv H
  end.
  destruct (link_globdefs lang_tgt def1'_tgt def2'_tgt) as [defs_tgt|] eqn:Hdefs_tgt.
  - eexists. split; constructor; simpl; auto.
    apply
      (@PTree_rel_PTree_elements _ _
         (fun g1 g2 =>
            exists p,
              program_linkeq lang_src p {| prog_defs := PTree.elements defs_src; prog_main := prog_main1 |} /\
              grel p g1 g2)).
    constructor. intro.
    eapply gtlink_globdefs in Hdefs_src. instantiate (1 := i) in Hdefs_src.
    eapply gtlink_globdefs in Hdefs_tgt. instantiate (1 := i) in Hdefs_tgt.
    inv H1. specialize (H i). inv H2. specialize (H0 i).
    revert H H0 Hdefs_src Hdefs_tgt. unfold globdefT in *. simpl in *.
    destruct (def1'_src ! i), (def1'_tgt ! i), (def2'_src ! i), (def2'_tgt ! i), (defs_src ! i), (defs_tgt ! i); intros H1 H2 H3 H4; subst; auto; clarify.
    + destruct H3 as [[H3 ?]|[H3 ?]], H4 as [[H4 ?]|[H4 ?]]; subst.
      * destruct H2 as [p [Hp Hg]]. eexists. split; [|eauto].
        etransitivity; eauto.
      * destruct H1 as [p1 [Hp1 H1]].
        destruct H2 as [p2 [Hp2 H2]].
        exploit linkable_grel_linkable; try etransitivity; eauto. intro X.
        inv H4; inv X.
        { inv Hv; inv Hv0; clarify.
          inv H1; inv H2; clarify.
          eexists. split; [reflexivity|].
          eapply grel_ef; eauto.
        }
        { inv H1. inv H2. monadInv Hv1. monadInv Hv2.
          inv Hv. simpl in *. subst. inv Hv0. simpl in *.
          destruct gv_src, gv_src0. simpl in *.
          clear Hreadonly0 Hvolatile0. subst.
          eexists. split; [reflexivity|].
          eapply grel_gv; eauto.
          unfold transf_globvar. simpl. rewrite EQ0. auto.
        }
      * destruct H1 as [p1 [Hp1 H1]].
        destruct H2 as [p2 [Hp2 H2]].
        exploit linkable_grel_linkable; try etransitivity; eauto. intro X.
        inv H4; inv X.
        { inv Hv; inv Hv0; clarify.
          inv H1; inv H2; clarify.
          eexists. split; [reflexivity|].
          eapply grel_ef; eauto.
        }
        { inv H1. inv H2. monadInv Hv1. monadInv Hv2.
          inv Hv. simpl in *. subst. inv Hv0. simpl in *.
          destruct gv_src, gv_src0. simpl in *.
          clear Hreadonly0 Hvolatile0. subst.
          eexists. split; [reflexivity|].
          eapply grel_gv; eauto.
          unfold transf_globvar. simpl. rewrite EQ. auto.
        }
      * destruct H1 as [p [Hp Hg]]. eexists. split; [|eauto].
        etransitivity; eauto.
    + destruct H1 as [p [Hp Hg]]. eexists. split; [|eauto].
      etransitivity; eauto.
    + destruct H2 as [p [Hp Hg]]. eexists. split; [|eauto].
      etransitivity; eauto.
  - apply gflink_globdefs in Hdefs_tgt. destruct Hdefs_tgt as [var [def1 [def2 [Hdef1 [Hdef2 [Hnl1 Hnl2]]]]]].
    inv H1. specialize (H var). rewrite Hdef1 in H.
    inv H2. specialize (H0 var). rewrite Hdef2 in H0.
    eapply gtlink_globdefs in Hdefs_src. instantiate (1 := var) in Hdefs_src.
    destruct (def1'_src ! var), (def2'_src ! var), (defs_src ! var);
      try match goal with
            | [H: False |- _] => inv H
          end.
    destruct Hdefs_src as [[Hl ?]|[Hl ?]]; subst.
    + contradict Hnl1.
      destruct H as [p1 [Hp1 H]].
      destruct H0 as [p2 [Hp2 H0]].
      eapply linkable_grel_linkable; try etransitivity; eauto.
    + contradict Hnl2.
      destruct H as [p1 [Hp1 H]].
      destruct H0 as [p2 [Hp2 H0]].
      eapply linkable_grel_linkable; try etransitivity; eauto.
Qed.

End SEPCOMP_RELATION.

Lemma sepcomp_rel_mor lang_src lang_tgt
      frel1 frel2 efrel1 efrel2 trans_v
      (FREL: frel1 <3= frel2)
      (EFREL: efrel1 <3= efrel2):
  @sepcomp_rel lang_src lang_tgt frel1 efrel1 trans_v <2= @sepcomp_rel lang_src lang_tgt frel2 efrel2 trans_v.
Proof.
  intros. inv PR. constructor; auto.
  eapply list_forall2_imply; eauto. simpl. intros. des.
  split; auto. eexists. split; eauto.
  destruct v1, v2. simpl in *. subst.
  inv H3.
  - eapply grel_f; eauto.
  - eapply grel_ef; eauto.
  - eapply grel_gv; eauto.
Qed.

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

Variable transf_fT: lang_src.(progT) -> fT_src -> res fT_tgt.
Variable transf_efT: lang_src.(progT) -> efT_src -> res efT_tgt.
Variable transf_vT: vT_src -> res vT_tgt.

Let transf_fundefT (prog_src:lang_src.(progT)) (fd_src:fundefT_src): res fundefT_tgt :=
  match fundefT_src.(Fundef_equiv).(AtoB) fd_src with
    | inl f =>
      bind
        (transf_fT prog_src f)
        (fun f => OK (fundefT_tgt.(Fundef_equiv).(BtoA) (inl f)))
    | inr ef =>
      bind
        (transf_efT prog_src ef)
        (fun ef => OK (fundefT_tgt.(Fundef_equiv).(BtoA) (inr ef)))
  end.

Variable p: lang_src.(progT).
Variable p': lang_tgt.(progT).

Section TRANSF.

Hypothesis TRANSF: transform_partial_program2 (transf_fundefT p) transf_vT p = OK p'.

Lemma transf_partial2_sepcomp_rel:
  @sepcomp_rel
    lang_src lang_tgt
    (fun p f tf => transf_fT p f = OK tf)
    (fun p ef tef => transf_efT p ef = OK tef)
    transf_vT
    p p'.
Proof.
  destruct p as [defs ?], p' as [tdefs ?].
  unfold transform_partial_program2 in TRANSF. monadInv TRANSF.
  constructor; auto.
  revert tdefs EQ. generalize defs at 1 3 as fdefs.
  induction defs; simpl; intros fdefs tdefs Hdefs.
  { inv Hdefs. constructor. }
  destruct a. destruct g.
  - match goal with
      | [H: match ?x with OK _ => _ | Error _ => _ end = OK _ |- _] =>
        destruct x as [tf|] eqn:Hf; [|inv H]
    end.
    monadInv Hdefs. constructor; simpl.
    + split; auto. eexists. split; [reflexivity|].
      unfold transf_fundefT in Hf. destruct (fundefT_src.(AtoB) f) as [func|efunc] eqn:Hf'; monadInv Hf.
      * eapply grel_f; eauto. apply HBAB.
      * eapply grel_ef; eauto. apply HBAB.
    + apply IHdefs. auto.
  - match goal with
      | [H: match ?x with OK _ => _ | Error _ => _ end = OK _ |- _] =>
        destruct x as [tf|] eqn:Hf; [|inv H]
    end.
    monadInv Hdefs. constructor; simpl.
    + split; auto. eexists. split; [reflexivity|].
      constructor. auto.
    + apply IHdefs. auto.
Qed.

End TRANSF.

Section INITIAL.

Hypothesis Hsepcomp_rel:
  @sepcomp_rel
    lang_src lang_tgt
    (fun p f tf => transf_fT p f = OK tf)
    (fun p ef tef => transf_efT p ef = OK tef)
    transf_vT
    p p'.

Let prog_match:
  match_program
    (fun fd tfd =>
       exists prog_src,
         program_linkeq lang_src prog_src p /\
         transf_fundefT prog_src fd = OK tfd)
    (fun info tinfo => transf_vT info = OK tinfo)
    nil p.(prog_main)
    p p'.
Proof.
  destruct p as [defs ?], p' as [defs' ?].
  inv Hsepcomp_rel. simpl in *. subst.
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
    unfold transf_fundefT. simpl in *.
    rewrite Hf_src, Hf. simpl. rewrite <- Hf_tgt, HABA. auto.
  - apply match_glob_fun. eexists. split; eauto.
    unfold transf_fundefT. simpl in *.
    rewrite Hef_src, Hef. simpl. rewrite <- Hef_tgt, HABA. auto.
  - unfold transf_globvar in Hv. monadInv Hv. simpl in *. destruct gv_src.
    apply match_glob_var. auto.
Qed.

Theorem find_funct_ptr_transf_partial2:
  forall (b: block) (f: fundefT_src),
  Genv.find_funct_ptr (Genv.globalenv p) b = Some f ->
  exists f',
  Genv.find_funct_ptr (Genv.globalenv p') b = Some f' /\ 
  exists prog_src,
    program_linkeq lang_src prog_src p /\
    transf_fundefT prog_src f = OK f'.
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
    transf_fundefT prog_src f = OK tf.
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
    transf_fundefT prog_src f = OK f'.
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
    transf_fundefT prog_src f = OK tf.
Proof.
  intros. 
  exploit Genv.find_funct_rev_match. eexact prog_match. eauto. 
  intros [[f [X Y]]|X]; [|inv X]. exists f; auto.
Qed.

Theorem find_var_info_transf_partial2:
  forall (b: block) (v: globvar vT_src),
  Genv.find_var_info (Genv.globalenv p) b = Some v ->
  exists v',
  Genv.find_var_info (Genv.globalenv p') b = Some v' /\ transf_globvar transf_vT v = OK v'.
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
  Genv.find_var_info (Genv.globalenv p) b = Some v /\ transf_globvar transf_vT v = OK v'.
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
  intros. erewrite Genv.init_mem_match; eauto. eauto.
Qed.

End INITIAL.

End TRANSF_PARTIAL2.

Section TRANSF_PARTIAL2_OPTIONALLY.

Variable (sigT:Sig).
Variable (fT:F sigT).
Variable (efT:EF sigT).
Variable (fundefT:Fundef fT efT).
Variable (vT:V).

Let lang := mkLanguage fundefT vT.

Variable transf_fT: lang.(progT) -> fT -> res fT.
Variable transf_efT: lang.(progT) -> efT -> res efT.
Variable transf_vT: vT -> res vT.

Let transf_fundefT (prog:lang.(progT)) (fd:fundefT): res fundefT :=
  match fundefT.(Fundef_equiv).(AtoB) fd with
    | inl f =>
      bind
        (transf_fT prog f)
        (fun f => OK (fundefT.(Fundef_equiv).(BtoA) (inl f)))
    | inr ef =>
      bind
        (transf_efT prog ef)
        (fun ef => OK (fundefT.(Fundef_equiv).(BtoA) (inr ef)))
  end.

Variable p: lang.(progT).
Variable p': lang.(progT).

Section TRANSF.

Hypothesis TRANSF: transform_partial_program2 (transf_fundefT p) transf_vT p = OK p'.

Lemma transf_partial2_optionally_sepcomp_rel:
  @sepcomp_rel
    lang lang
    (fun p f tf => transf_fT p f = OK tf \/ f = tf)
    (fun p ef tef => transf_efT p ef = OK tef)
    transf_vT
    p p'.
Proof.
  destruct p as [defs ?], p' as [tdefs ?].
  unfold transform_partial_program2 in TRANSF. monadInv TRANSF.
  constructor; auto.
  revert tdefs EQ. generalize defs at 1 3 as fdefs.
  induction defs; simpl; intros fdefs tdefs Hdefs.
  { inv Hdefs. constructor. }
  destruct a. destruct g.
  - match goal with
      | [H: match ?x with OK _ => _ | Error _ => _ end = OK _ |- _] =>
        destruct x as [tf|] eqn:Hf; [|inv H]
    end.
    monadInv Hdefs. constructor; simpl.
    + split; auto. eexists. split; [reflexivity|].
      unfold transf_fundefT in Hf. destruct (fundefT.(AtoB) f) as [func|efunc] eqn:Hf'; monadInv Hf.
      * eapply grel_f. eauto. apply HBAB. left. auto.
      * eapply grel_ef; eauto. apply HBAB.
    + apply IHdefs. auto.
  - match goal with
      | [H: match ?x with OK _ => _ | Error _ => _ end = OK _ |- _] =>
        destruct x as [tf|] eqn:Hf; [|inv H]
    end.
    monadInv Hdefs. constructor; simpl.
    + split; auto. eexists. split; [reflexivity|].
      constructor. auto.
    + apply IHdefs. auto.
Qed.

End TRANSF.

Section TRANSF_ID.

Hypothesis TRANSF: p = p'.

Lemma transf_partial2_optionally_sepcomp_rel_identical:
  @sepcomp_rel
    lang lang
    (fun p f tf => transf_fT p f = OK tf \/ f = tf)
    (fun p ef tef => (fun _ ef => OK ef) p ef = OK tef)
    (@OK vT)
    p p'.
Proof.
  destruct p as [defs ?], p' as [tdefs ?].
  unfold transform_partial_program2 in TRANSF. inv TRANSF.
  constructor; auto.
  generalize tdefs at 1 as fdefs.
  revert tdefs.
  induction tdefs; simpl.
  { constructor. }
  destruct a. destruct g.
  - constructor; simpl.
    + split; auto. eexists. split; [reflexivity|].
      unfold transf_fundefT. destruct (fundefT.(AtoB) f) as [func|efunc] eqn:Hf'.
      * eapply grel_f; eauto.
      * eapply grel_ef; eauto.
    + apply IHtdefs.
  - constructor; simpl.
    + split; auto. eexists. split; [reflexivity|].
      constructor. unfold transf_globvar. simpl. destruct v; auto.
    + apply IHtdefs.
Qed.

End TRANSF_ID.

Section INITIAL.

Hypothesis Hsepcomp_rel:
  @sepcomp_rel
    lang lang
    (fun p f tf => transf_fT p f = OK tf \/ f = tf)
    (fun p ef tef => transf_efT p ef = OK tef)
    transf_vT
    p p'.

Let prog_match:
  match_program
    (fun fd tfd =>
       (exists prog,
          program_linkeq lang prog p /\
          transf_fundefT prog fd = OK tfd) \/
       fd = tfd)
    (fun info tinfo => transf_vT info = OK tinfo)
    nil p.(prog_main)
    p p'.
Proof.
  destruct p as [defs ?], p' as [defs' ?].
  inv Hsepcomp_rel. simpl in *. subst.
  revert defs' Hdefs. generalize defs at 1 3 as fdefs.
  induction defs; intros fdefs defs' Hdefs.
  { inv Hdefs. constructor; auto. exists nil. split; auto. constructor. }
  inv Hdefs. destruct a, b1, H1 as [? H1]. simpl in *. subst.
  eapply IHdefs in H3. destruct H3 as [H3 ?]. split; [|auto].
  destruct H3 as [? H3]. simpl in *. rewrite app_nil_r in *.
  destruct H3 as [H3 ?]. subst.
  eexists. rewrite app_nil_r. split; auto.
  constructor; auto.
  destruct H1 as [prog [Hprog H1]]. inv H1.
  - apply match_glob_fun. destruct Hf as [Hf|Hf]; subst.
    + left. eexists. split; eauto.
      unfold transf_fundefT. simpl in *.
      rewrite Hf_src, Hf. simpl. rewrite <- Hf_tgt, HABA. auto.
    + right. rewrite <- Hf_tgt in Hf_src.
      eapply EquivalentType_AtoB_inj. eauto.
  - apply match_glob_fun. left. eexists. split; eauto.
    unfold transf_fundefT. simpl in *.
    rewrite Hef_src, Hef. simpl. rewrite <- Hef_tgt, HABA. auto.
  - unfold transf_globvar in Hv. monadInv Hv. simpl in *. destruct gv_src.
    apply match_glob_var. auto.
Qed.

Theorem find_funct_ptr_transf_partial2_optionally:
  forall (b: block) (f: fundefT),
  Genv.find_funct_ptr (Genv.globalenv p) b = Some f ->
  exists f',
  Genv.find_funct_ptr (Genv.globalenv p') b = Some f' /\ 
  ((exists prog,
      program_linkeq lang prog p /\
      transf_fundefT prog f = OK f') \/
   f = f').
Proof.
  intros. 
  exploit Genv.find_funct_ptr_match. eexact prog_match. eauto. 
  intros [tf [X Y]]. exists tf; auto.
Qed.

Theorem find_funct_ptr_rev_transf_partial2_optionally:
  forall (b: block) (tf: fundefT),
  Genv.find_funct_ptr (Genv.globalenv p') b = Some tf ->
  exists f, Genv.find_funct_ptr (Genv.globalenv p) b = Some f /\ 
  ((exists prog,
      program_linkeq lang prog p /\
      transf_fundefT prog f = OK tf) \/
   f = tf).
Proof.
  intros. 
  exploit Genv.find_funct_ptr_rev_match. eexact prog_match. eauto. 
  destruct (plt b (Genv.genv_next (Genv.globalenv p))); [|intro X; inv X].
  intros [f [X Y]]. exists f; auto.
Qed.

Theorem find_funct_transf_partial2_optionally:
  forall (v: val) (f: fundefT),
  Genv.find_funct (Genv.globalenv p) v = Some f ->
  exists f',
  Genv.find_funct (Genv.globalenv p') v = Some f' /\ 
  ((exists prog,
      program_linkeq lang prog p /\
      transf_fundefT prog f = OK f') \/
   f = f').
Proof.
  intros. 
  exploit Genv.find_funct_match. eexact prog_match. eauto. 
  intros [tf [X Y]]. exists tf; auto.
Qed.

Theorem find_funct_rev_transf_partial2_optionally:
  forall (v: val) (tf: fundefT),
  Genv.find_funct (Genv.globalenv p') v = Some tf ->
  exists f, Genv.find_funct (Genv.globalenv p) v = Some f /\ 
  ((exists prog,
      program_linkeq lang prog p /\
      transf_fundefT prog f = OK tf) \/
   f = tf).
Proof.
  intros. 
  exploit Genv.find_funct_rev_match. eexact prog_match. eauto. 
  intros [[f [X Y]]|X]; [|inv X]. exists f; auto.
Qed.

Theorem find_var_info_transf_partial2_optionally:
  forall (b: block) (v: globvar vT),
  Genv.find_var_info (Genv.globalenv p) b = Some v ->
  exists v',
  Genv.find_var_info (Genv.globalenv p') b = Some v' /\ transf_globvar transf_vT v = OK v'.
Proof.
  intros. 
  exploit Genv.find_var_info_match. eexact prog_match. eauto. intros [tv [X Y]]. 
  exists tv; split; auto. inv Y. unfold transf_globvar; simpl.
  rewrite H0; simpl. auto.
Qed.

Theorem find_var_info_rev_transf_partial2_optionally:
  forall (b: block) (v': globvar vT),
  Genv.find_var_info (Genv.globalenv p') b = Some v' ->
  exists v,
  Genv.find_var_info (Genv.globalenv p) b = Some v /\ transf_globvar transf_vT v = OK v'.
Proof.
  intros. 
  exploit Genv.find_var_info_rev_match. eexact prog_match. eauto.
  destruct (plt b (Genv.genv_next (Genv.globalenv p))); [|intro X; inv X].
  intros [v [X Y]]. exists v; split; auto. inv Y. unfold transf_globvar; simpl. 
  rewrite H0; simpl. auto.
Qed.

Theorem find_symbol_transf_partial2_optionally:
  forall (s: ident),
  Genv.find_symbol (Genv.globalenv p') s = Genv.find_symbol (Genv.globalenv p) s.
Proof.
  intros. eapply Genv.find_symbol_match. eexact prog_match. auto.
Qed.

Theorem init_mem_transf_partial2_optionally:
  forall m, Genv.init_mem p = Some m -> Genv.init_mem p' = Some m.
Proof.
  intros. erewrite Genv.init_mem_match; eauto. eauto.
Qed.

End INITIAL.

End TRANSF_PARTIAL2_OPTIONALLY.

Section TRANSF_PARTIAL.

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

Variable transf_fT: lang_src.(progT) -> fT_src -> res fT_tgt.
Variable transf_efT: lang_src.(progT) -> efT_src -> res efT_tgt.

Let transf_fundefT (prog_src:lang_src.(progT)) (fd_src:fundefT_src): res fundefT_tgt :=
  match fundefT_src.(Fundef_equiv).(AtoB) fd_src with
    | inl f =>
      bind
        (transf_fT prog_src f)
        (fun f => OK (fundefT_tgt.(Fundef_equiv).(BtoA) (inl f)))
    | inr ef =>
      bind
        (transf_efT prog_src ef)
        (fun ef => OK (fundefT_tgt.(Fundef_equiv).(BtoA) (inr ef)))
  end.

Variable p: lang_src.(progT).
Variable p': lang_tgt.(progT).

Section TRANSF.

Hypothesis TRANSF: transform_partial_program (transf_fundefT p) p = OK p'.

Lemma transf_partial_sepcomp_rel:
  @sepcomp_rel
    lang_src lang_tgt
    (fun p f tf => transf_fT p f = OK tf)
    (fun p ef tef => transf_efT p ef = OK tef)
    (@OK _)
    p p'.
Proof.
  apply transf_partial2_sepcomp_rel; eauto.
Qed.

End TRANSF.

Section INITIAL.

Hypothesis Hsepcomp_rel:
  @sepcomp_rel
    lang_src lang_tgt
    (fun p f tf => transf_fT p f = OK tf)
    (fun p ef tef => transf_efT p ef = OK tef)
    (@OK _)
    p p'.

Theorem find_funct_ptr_transf_partial:
  forall (b: block) (f: fundefT_src),
  Genv.find_funct_ptr (Genv.globalenv p) b = Some f ->
  exists f',
  Genv.find_funct_ptr (Genv.globalenv p') b = Some f' /\ 
  exists prog_src,
    program_linkeq lang_src prog_src p /\
    transf_fundefT prog_src f = OK f'.
Proof (find_funct_ptr_transf_partial2 _ _ Hsepcomp_rel).

Theorem find_funct_ptr_rev_transf_partial:
  forall (b: block) (tf: fundefT_tgt),
  Genv.find_funct_ptr (Genv.globalenv p') b = Some tf ->
  exists f, Genv.find_funct_ptr (Genv.globalenv p) b = Some f /\ 
  exists prog_src,
    program_linkeq lang_src prog_src p /\
    transf_fundefT prog_src f = OK tf.
Proof (find_funct_ptr_rev_transf_partial2 _ _ Hsepcomp_rel).

Theorem find_funct_transf_partial:
  forall (v: val) (f: fundefT_src),
  Genv.find_funct (Genv.globalenv p) v = Some f ->
  exists f',
  Genv.find_funct (Genv.globalenv p') v = Some f' /\ 
  exists prog_src,
    program_linkeq lang_src prog_src p /\
    transf_fundefT prog_src f = OK f'.
Proof (find_funct_transf_partial2 _ _ Hsepcomp_rel).

Theorem find_funct_rev_transf_partial:
  forall (v: val) (tf: fundefT_tgt),
  Genv.find_funct (Genv.globalenv p') v = Some tf ->
  exists f, Genv.find_funct (Genv.globalenv p) v = Some f /\ 
  exists prog_src,
    program_linkeq lang_src prog_src p /\
    transf_fundefT prog_src f = OK tf.
Proof (find_funct_rev_transf_partial2 _ _ Hsepcomp_rel).

Theorem find_var_info_transf_partial:
  forall (b: block),
  Genv.find_var_info (Genv.globalenv p') b = Genv.find_var_info (Genv.globalenv p) b.
Proof.
  intros. destruct (Genv.find_var_info (Genv.globalenv p) b) as [v|] eqn:Hg.
  - exploit find_var_info_transf_partial2; try apply Hsepcomp_rel; eauto.
    simpl. intros [v'' [Hv'' X]]. destruct v. inv X. auto.
  - destruct (Genv.find_var_info (Genv.globalenv p') b) as [v|] eqn:Hg'; [|auto].
    exploit find_var_info_rev_transf_partial2; try apply Hsepcomp_rel; eauto.
    simpl. intros [v'' [Hv'' X]].
    simpl in *. rewrite Hg in Hv''. inv Hv''.
Qed.

Theorem find_symbol_transf_partial:
  forall (s: ident),
  Genv.find_symbol (Genv.globalenv p') s = Genv.find_symbol (Genv.globalenv p) s.
Proof (find_symbol_transf_partial2 _ _ Hsepcomp_rel).

Theorem init_mem_transf_partial:
  forall m, Genv.init_mem p = Some m -> Genv.init_mem p' = Some m.
Proof (init_mem_transf_partial2 _ _ Hsepcomp_rel).

End INITIAL.

End TRANSF_PARTIAL.

Section TRANSF_PARTIAL_OPTIONALLY.

Variable (sigT:Sig).
Variable (fT:F sigT).
Variable (efT:EF sigT).
Variable (fundefT:Fundef fT efT).
Variable (vT:V).

Let lang := mkLanguage fundefT vT.

Variable transf_fT: lang.(progT) -> fT -> res fT.
Variable transf_efT: lang.(progT) -> efT -> res efT.

Let transf_fundefT (prog:lang.(progT)) (fd:fundefT): res fundefT :=
  match fundefT.(Fundef_equiv).(AtoB) fd with
    | inl f =>
      bind
        (transf_fT prog f)
        (fun f => OK (fundefT.(Fundef_equiv).(BtoA) (inl f)))
    | inr ef =>
      bind
        (transf_efT prog ef)
        (fun ef => OK (fundefT.(Fundef_equiv).(BtoA) (inr ef)))
  end.

Variable p: lang.(progT).
Variable p': lang.(progT).

Section TRANSF.

Hypothesis TRANSF: transform_partial_program (transf_fundefT p) p = OK p'.

Lemma transf_partial_optionally_sepcomp_rel:
  @sepcomp_rel
    lang lang
    (fun p f tf => transf_fT p f = OK tf \/ f = tf)
    (fun p ef tef => transf_efT p ef = OK tef)
    (@OK _)
    p p'.
Proof.
  apply transf_partial2_optionally_sepcomp_rel; eauto.
Qed.

End TRANSF.

Section TRANSF_ID.

Hypothesis TRANSF: p = p'.

Lemma transf_partial_optionally_sepcomp_rel_identical:
  @sepcomp_rel
    lang lang
    (fun p f tf => transf_fT p f = OK tf \/ f = tf)
    (fun p ef tef => (fun _ ef => OK ef) p ef = OK tef)
    (@OK _)
    p p'.
Proof.
  apply transf_partial2_optionally_sepcomp_rel_identical; eauto.
Qed.
  
End TRANSF_ID.

Section INITIAL.

Hypothesis Hsepcomp_rel:
  @sepcomp_rel
    lang lang
    (fun p f tf => transf_fT p f = OK tf \/ f = tf)
    (fun p ef tef => transf_efT p ef = OK tef)
    (@OK _)
    p p'.

Theorem find_funct_ptr_transf_partial_optionally:
  forall (b: block) (f: fundefT),
  Genv.find_funct_ptr (Genv.globalenv p) b = Some f ->
  exists f',
  Genv.find_funct_ptr (Genv.globalenv p') b = Some f' /\ 
  ((exists prog,
      program_linkeq lang prog p /\
      transf_fundefT prog f = OK f') \/
   f = f').
Proof (find_funct_ptr_transf_partial2_optionally _ _ Hsepcomp_rel).

Theorem find_funct_ptr_rev_transf_partial_optionally:
  forall (b: block) (tf: fundefT),
  Genv.find_funct_ptr (Genv.globalenv p') b = Some tf ->
  exists f, Genv.find_funct_ptr (Genv.globalenv p) b = Some f /\ 
  ((exists prog,
      program_linkeq lang prog p /\
      transf_fundefT prog f = OK tf) \/
   f = tf).
Proof (find_funct_ptr_rev_transf_partial2_optionally _ _ Hsepcomp_rel).

Theorem find_funct_transf_partial_optionally:
  forall (v: val) (f: fundefT),
  Genv.find_funct (Genv.globalenv p) v = Some f ->
  exists f',
  Genv.find_funct (Genv.globalenv p') v = Some f' /\ 
  ((exists prog,
      program_linkeq lang prog p /\
      transf_fundefT prog f = OK f') \/
   f = f').
Proof (find_funct_transf_partial2_optionally _ _ Hsepcomp_rel).

Theorem find_funct_rev_transf_partial_optionally:
  forall (v: val) (tf: fundefT),
  Genv.find_funct (Genv.globalenv p') v = Some tf ->
  exists f, Genv.find_funct (Genv.globalenv p) v = Some f /\ 
  ((exists prog,
      program_linkeq lang prog p /\
      transf_fundefT prog f = OK tf) \/
   f = tf).
Proof (find_funct_rev_transf_partial2_optionally _ _ Hsepcomp_rel).

Theorem find_var_info_transf_partial_optionally:
  forall (b: block),
  Genv.find_var_info (Genv.globalenv p') b = Genv.find_var_info (Genv.globalenv p) b.
Proof.
  intros. destruct (Genv.find_var_info (Genv.globalenv p) b) as [v|] eqn:Hg.
  - exploit find_var_info_transf_partial2_optionally; try apply Hsepcomp_rel; eauto.
    simpl. intros [v'' [Hv'' X]]. destruct v. inv X. auto.
  - destruct (Genv.find_var_info (Genv.globalenv p') b) as [v|] eqn:Hg'; [|auto].
    exploit find_var_info_rev_transf_partial2_optionally; try apply Hsepcomp_rel; eauto.
    simpl. intros [v'' [Hv'' X]].
    simpl in *. rewrite Hg in Hv''. inv Hv''.
Qed.

Theorem find_symbol_transf_partial_optionally:
  forall (s: ident),
  Genv.find_symbol (Genv.globalenv p') s = Genv.find_symbol (Genv.globalenv p) s.
Proof (find_symbol_transf_partial2_optionally _ _ Hsepcomp_rel).

Theorem init_mem_transf_partial_optionally:
  forall m, Genv.init_mem p = Some m -> Genv.init_mem p' = Some m.
Proof (init_mem_transf_partial2_optionally _ _ Hsepcomp_rel).

End INITIAL.

End TRANSF_PARTIAL_OPTIONALLY.

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

Variable transf_fT: lang_src.(progT) -> fT_src -> fT_tgt.
Variable transf_efT: lang_src.(progT) -> efT_src -> efT_tgt.

Let transf_fundefT (prog_src:lang_src.(progT)) (fd_src:fundefT_src): fundefT_tgt :=
  match fundefT_src.(Fundef_equiv).(AtoB) fd_src with
    | inl f =>
      fundefT_tgt.(Fundef_equiv).(BtoA) (inl (transf_fT prog_src f))
    | inr ef =>
      fundefT_tgt.(Fundef_equiv).(BtoA) (inr (transf_efT prog_src ef))
  end.

Variable p: lang_src.(progT).
Variable tp: lang_tgt.(progT).

Section TRANSF.

Hypothesis TRANSF: transform_program (transf_fundefT p) p = tp.

Lemma transf_program_sepcomp_rel:
  @sepcomp_rel
    lang_src lang_tgt
    (fun p f tf => transf_fT p f = tf)
    (fun p ef tef => transf_efT p ef = tef)
    (@OK _)
    p tp.
Proof.
  destruct p as [defs ?], tp as [tdefs ?]. inv TRANSF.
  constructor; auto. simpl.
  generalize defs at 1 3 as fdefs.
  induction defs; simpl; intros fdefs; constructor.
  - split.
    + destruct a. destruct g; auto.
    + eexists. split; [reflexivity|].
      destruct a. simpl. destruct g.
      * unfold transf_fundefT. destruct (fundefT_src.(AtoB) f) as [func|efunc] eqn:Hf'.
        { eapply grel_f; eauto. apply HBAB. }
        { eapply grel_ef; eauto. apply HBAB. }
      * constructor. destruct v. auto.
  - apply IHdefs.
Qed.

End TRANSF.

Section INITIAL.

Hypothesis Hsepcomp_rel:
  @sepcomp_rel
    lang_src lang_tgt
    (fun p f tf => transf_fT p f = tf)
    (fun p ef tef => transf_efT p ef = tef)
    (@OK _)
    p tp.

Let prog_match:
  match_program
    (fun fd tfd =>
       exists prog_src,
         program_linkeq lang_src prog_src p /\
         transf_fundefT prog_src fd = tfd)
    (fun info tinfo => info = tinfo)
    nil p.(prog_main)
    p tp.
Proof.
  destruct p as [defs ?], tp as [defs' ?].
  inv Hsepcomp_rel. simpl in *. subst.
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
    unfold transf_fundefT. simpl in *.
    rewrite Hf_src, <- Hf_tgt. apply HABA.
  - apply match_glob_fun. eexists. split; eauto.
    unfold transf_fundefT. simpl in *.
    rewrite Hef_src, <- Hef_tgt. apply HABA.
  - unfold transf_globvar in Hv. monadInv Hv. inv EQ.
    simpl in *. destruct gv_src.
    apply match_glob_var. auto.
Qed.

Theorem find_funct_ptr_transf:
  forall (b: block) (f: fundefT_src),
  Genv.find_funct_ptr (Genv.globalenv p) b = Some f ->
  exists prog_src,
    program_linkeq lang_src prog_src p /\
    Genv.find_funct_ptr (Genv.globalenv tp) b = Some (transf_fundefT prog_src f).
Proof.
  intros. 
  exploit Genv.find_funct_ptr_match. eexact prog_match. eauto. 
  intros [tf [X [prog_src [Hprog_src Y]]]]. subst.
  eexists. split; eauto.
Qed.

Theorem find_funct_ptr_rev_transf:
  forall (b: block) (tf: fundefT_tgt),
  Genv.find_funct_ptr (Genv.globalenv tp) b = Some tf ->
  exists f, Genv.find_funct_ptr (Genv.globalenv p) b = Some f /\
            exists prog_src,
              program_linkeq lang_src prog_src p /\
              transf_fundefT prog_src f = tf.
Proof.
  intros. 
  exploit Genv.find_funct_ptr_rev_match. eexact prog_match. eauto. 
  destruct (plt b (Genv.genv_next (Genv.globalenv p))); [|intro X; inv X].
  intros [f [X Y]]. exists f; auto.
Qed.

Theorem find_funct_transf:
  forall (v: val) (f: fundefT_src),
  Genv.find_funct (Genv.globalenv p) v = Some f ->
  exists prog_src,
    program_linkeq lang_src prog_src p /\
    Genv.find_funct (Genv.globalenv tp) v = Some (transf_fundefT prog_src f).
Proof.
  intros. 
  exploit Genv.find_funct_match. eexact prog_match. eauto. 
  intros [tf [X [prog_src [Hprog_src Y]]]]. subst.
  eexists. split; eauto.
Qed.

Theorem find_funct_rev_transf:
  forall (v: val) (tf: fundefT_tgt),
  Genv.find_funct (Genv.globalenv tp) v = Some tf ->
  exists f, Genv.find_funct (Genv.globalenv p) v = Some f /\ 
            exists prog_src,
              program_linkeq lang_src prog_src p /\
              transf_fundefT prog_src f = tf.
Proof.
  intros. 
  exploit Genv.find_funct_rev_match. eexact prog_match. eauto. 
  intros [[f [X Y]]|X]; [|inv X]. exists f; auto.
Qed.

Theorem find_symbol_transf:
  forall (s: ident),
  Genv.find_symbol (Genv.globalenv tp) s = Genv.find_symbol (Genv.globalenv p) s.
Proof.
  intros. eapply Genv.find_symbol_match. eexact prog_match. auto.
Qed.

Theorem find_var_info_transf:
  forall (b: block),
  Genv.find_var_info (Genv.globalenv tp) b = Genv.find_var_info (Genv.globalenv p) b.
Proof.
  intros. destruct (Genv.find_var_info (Genv.globalenv p) b) as [v|] eqn:Hg.
  - exploit Genv.find_var_info_match. eexact prog_match. eauto. intros [tv [X Y]].
    inv Y. auto.
  - destruct (Genv.find_var_info (Genv.globalenv tp) b) as [v|] eqn:Hg'; [|auto].
    exploit Genv.find_var_info_rev_match. eexact prog_match. eauto.
    destruct (plt b (Genv.genv_next (Genv.globalenv p))); [|intro X; inv X].
    intros [v' [X Y]]. rewrite Hg in X. inv X.
Qed.

Theorem init_mem_transf:
  forall m, Genv.init_mem p = Some m -> Genv.init_mem tp = Some m.
Proof.
  intros. erewrite Genv.init_mem_match; eauto. eauto.
Qed.

End INITIAL.

End TRANSF_PROGRAM.

Section TRANSF_PROGRAM_OPTIONALLY.

Variable (sigT:Sig).
Variable (fT:F sigT).
Variable (efT:EF sigT).
Variable (fundefT:Fundef fT efT).
Variable (vT:V).

Let lang := mkLanguage fundefT vT.

Variable transf_fT: lang.(progT) -> fT -> fT.
Variable transf_efT: lang.(progT) -> efT -> efT.

Let transf_fundefT (prog:lang.(progT)) (fd:fundefT): fundefT :=
  match fundefT.(Fundef_equiv).(AtoB) fd with
    | inl f =>
      fundefT.(Fundef_equiv).(BtoA) (inl (transf_fT prog f))
    | inr ef =>
      fundefT.(Fundef_equiv).(BtoA) (inr (transf_efT prog ef))
  end.

Variable p: lang.(progT).
Variable tp: lang.(progT).

Section TRANSF.

Hypothesis TRANSF: transform_program (transf_fundefT p) p = tp.

Lemma transf_program_optionally_sepcomp_rel:
  @sepcomp_rel
    lang lang
    (fun p f tf => transf_fT p f = tf \/ f = tf)
    (fun p ef tef => transf_efT p ef = tef)
    (@OK _)
    p tp.
Proof.
  destruct p as [defs ?], tp as [tdefs ?]. inv TRANSF.
  constructor; auto. simpl.
  generalize defs at 1 3 as fdefs.
  induction defs; simpl; intros fdefs; constructor.
  - split.
    + destruct a. destruct g; auto.
    + eexists. split; [reflexivity|].
      destruct a. simpl. destruct g.
      * unfold transf_fundefT. destruct (fundefT.(AtoB) f) as [func|efunc] eqn:Hf'.
        { eapply grel_f. eauto. apply HBAB. left. auto. }
        { eapply grel_ef; eauto. apply HBAB. }
      * constructor. destruct v. auto.
  - apply IHdefs.
Qed.

End TRANSF.

Section TRANSF_ID.

Hypothesis TRANSF: p = tp.

Lemma transf_program_optionally_sepcomp_rel_identical:
  @sepcomp_rel
    lang lang
    (fun p f tf => transf_fT p f = tf \/ f = tf)
    (fun p ef tef => ef = tef)
    (@OK _)
    p tp.
Proof.
  destruct p as [defs ?], tp as [tdefs ?]. inv TRANSF.
  constructor; auto. simpl.
  generalize tdefs at 1 as fdefs.
  induction tdefs; simpl; intros fdefs; constructor.
  - split; auto.
    eexists. split; [reflexivity| ].
    destruct a. simpl. destruct g.
    + unfold transf_fundefT. destruct (fundefT.(AtoB) f) as [func|efunc] eqn:Hf'.
      { eapply grel_f. eauto. eauto. right. auto. }
      { eapply grel_ef; eauto. }
    + constructor. destruct v. auto.
  - apply IHtdefs.
Qed.

End TRANSF_ID.

Section INITIAL.

Hypothesis Hsepcomp_rel:
  @sepcomp_rel
    lang lang
    (fun p f tf => transf_fT p f = tf \/ f = tf)
    (fun p ef tef => transf_efT p ef = tef)
    (@OK _)
    p tp.

Let prog_match:
  match_program
    (fun fd tfd =>
       (exists prog,
         program_linkeq lang prog p /\
         transf_fundefT prog fd = tfd) \/
       fd = tfd)
    (fun info tinfo => info = tinfo)
    nil p.(prog_main)
    p tp.
Proof.
  destruct p as [defs ?], tp as [defs' ?].
  inv Hsepcomp_rel. simpl in *. subst.
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
  - apply match_glob_fun. destruct Hf as [Hf|Hf]; subst.
    + left. eexists. split; eauto.
      unfold transf_fundefT. simpl in *.
      rewrite Hf_src, <- Hf_tgt. apply HABA.
    + right. rewrite <- Hf_tgt in Hf_src.
      eapply EquivalentType_AtoB_inj. eauto.
  - apply match_glob_fun. left. eexists. split; eauto.
    unfold transf_fundefT. simpl in *.
    rewrite Hef_src, <- Hef_tgt. apply HABA.
  - unfold transf_globvar in Hv. monadInv Hv. inv EQ.
    simpl in *. destruct gv_src.
    apply match_glob_var. auto.
Qed.

Theorem find_funct_ptr_transf_optionally:
  forall (b: block) (f: fundefT),
    Genv.find_funct_ptr (Genv.globalenv p) b = Some f ->
    exists f',
      Genv.find_funct_ptr (Genv.globalenv tp) b = Some f' /\
      ((exists prog,
         program_linkeq lang prog p /\
         (transf_fundefT prog f) = f') \/
      f = f').
Proof.
  intros. 
  exploit Genv.find_funct_ptr_match. eexact prog_match. eauto.
  intros [tf [X Y]]. exists tf; auto.
Qed.

Theorem find_funct_ptr_rev_transf_optionally:
  forall (b: block) (tf: fundefT),
    Genv.find_funct_ptr (Genv.globalenv tp) b = Some tf ->
    exists f, Genv.find_funct_ptr (Genv.globalenv p) b = Some f /\
              ((exists prog,
                  program_linkeq lang prog p /\
                  transf_fundefT prog f = tf)
               \/ f = tf).
Proof.
  intros. 
  exploit Genv.find_funct_ptr_rev_match. eexact prog_match. eauto. 
  destruct (plt b (Genv.genv_next (Genv.globalenv p))); [|intro X; inv X].
  intros [f [X Y]]. exists f; auto.
Qed.

Theorem find_funct_transf_optionally:
  forall (v: val) (f: fundefT),
  Genv.find_funct (Genv.globalenv p) v = Some f ->
  exists tf,
    Genv.find_funct (Genv.globalenv tp) v = Some tf /\
    ((exists prog,
        program_linkeq lang prog p /\
        (transf_fundefT prog f = tf)) \/
  f = tf).
Proof.
  intros. 
  exploit Genv.find_funct_match. eexact prog_match. eauto.
  intros [tf [X Y]]. subst.
  eexists. split; eauto.
Qed.

Theorem find_funct_rev_transf_optionally:
  forall (v: val) (tf: fundefT),
  Genv.find_funct (Genv.globalenv tp) v = Some tf ->
  exists f, Genv.find_funct (Genv.globalenv p) v = Some f /\ 
            ((exists prog,
              program_linkeq lang prog p /\
              transf_fundefT prog f = tf) \/
             f = tf).
Proof.
  intros. 
  exploit Genv.find_funct_rev_match. eexact prog_match. eauto. 
  intros [[f [X Y]]|X]; [|inv X]. exists f; auto.
Qed.

Theorem find_symbol_transf_optionally:
  forall (s: ident),
  Genv.find_symbol (Genv.globalenv tp) s = Genv.find_symbol (Genv.globalenv p) s.
Proof.
  intros. eapply Genv.find_symbol_match. eexact prog_match. auto.
Qed.

Theorem find_var_info_transf_optionally:
  forall (b: block),
  Genv.find_var_info (Genv.globalenv tp) b = Genv.find_var_info (Genv.globalenv p) b.
Proof.
  intros. destruct (Genv.find_var_info (Genv.globalenv p) b) as [v|] eqn:Hg.
  - exploit Genv.find_var_info_match. eexact prog_match. eauto. intros [tv [X Y]].
    inv Y. auto.
  - destruct (Genv.find_var_info (Genv.globalenv tp) b) as [v|] eqn:Hg'; [|auto].
    exploit Genv.find_var_info_rev_match. eexact prog_match. eauto.
    destruct (plt b (Genv.genv_next (Genv.globalenv p))); [|intro X; inv X].
    intros [v' [X Y]]. rewrite Hg in X. inv X.
Qed.

Theorem init_mem_transf_optionally:
  forall m, Genv.init_mem p = Some m -> Genv.init_mem tp = Some m.
Proof.
  intros. erewrite Genv.init_mem_match; eauto. eauto.
Qed.

End INITIAL.

End TRANSF_PROGRAM_OPTIONALLY.
