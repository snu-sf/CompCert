Require Import RelationClasses.
Require String.
Require Import Coqlib Coqlib_linker.
Require Import Maps_linker.
Require Import Integers Floats Values AST Globalenvs.
Require Import LinkerSpecification LinkerProp Linkeq.
Require Import Errors.

Set Implicit Arguments.


(* lifting function simulation to program simulation *)
Section PROGRAM_SIM.

Variable (Fundef_src F_src EF_src V_src:Type).
Variable (fundef_src_dec: FundefDec Fundef_src F_src EF_src).
Variable (EF_src_dec: forall (v1 v2:EF_src), {v1 = v2} + {v1 <> v2}).
Variable (V_src_dec: forall (v1 v2:V_src), {v1 = v2} + {v1 <> v2}).

Variable (Fundef_tgt F_tgt EF_tgt V_tgt:Type).
Variable (fundef_tgt_dec: FundefDec Fundef_tgt F_tgt EF_tgt).
Variable (EF_tgt_dec: forall (v1 v2:EF_tgt), {v1 = v2} + {v1 <> v2}).
Variable (V_tgt_dec: forall (v1 v2:V_tgt), {v1 = v2} + {v1 <> v2}).

Variable (transf_EF: forall (ef:EF_src), res EF_tgt).
Variable (transf_V: forall (v:V_src), res V_tgt).
Definition V_sim (v_src:V_src) (v_tgt:V_tgt) := transf_V v_src = OK v_tgt.

Parameter F_sim: forall
                   (defs_src:PTree.t (globdef Fundef_src V_src))
                   (defs_tgt:PTree.t (globdef Fundef_tgt V_tgt))
                   (f_src:F_src) (f_tgt:F_tgt), Prop.

(** definition *)
Inductive globfun_sim
          (defs_src:PTree.t (globdef Fundef_src V_src))
          (defs_tgt:PTree.t (globdef Fundef_tgt V_tgt))
          (g_src:Fundef_src) (g_tgt:Fundef_tgt): Prop :=
| globfun_sim_i
    f_src f_tgt
    (Hsrc: fundef_src_dec g_src = inl f_src)
    (Htgt: fundef_tgt_dec g_tgt = inl f_tgt)
    (Hsim: forall fdefs_src fdefs_tgt
                  (Hfdefs_src: globdefs_linkeq fundef_src_dec defs_src fdefs_src)
                  (Hfdefs_tgt: globdefs_linkeq fundef_tgt_dec defs_tgt fdefs_tgt),
             F_sim fdefs_src fdefs_tgt f_src f_tgt)
| globfun_sim_e
    ef_src ef_tgt (Hef: transf_EF ef_src = OK ef_tgt)
    (Hsrc: fundef_src_dec g_src = inr ef_src)
    (Htgt: fundef_tgt_dec g_tgt = inr ef_tgt)
.

Inductive globdef_sim
          (defs_src:PTree.t (globdef Fundef_src V_src))
          (defs_tgt:PTree.t (globdef Fundef_tgt V_tgt)):
  forall (g_src:globdef Fundef_src V_src) (g_tgt:globdef Fundef_tgt V_tgt), Prop :=
| globdef_sim_fun
    f_src f_tgt (Hf: globfun_sim defs_src defs_tgt f_src f_tgt):
    globdef_sim defs_src defs_tgt (Gfun f_src) (Gfun f_tgt)
| globdef_sim_var
    v_src v_tgt (Hv: transf_globvar transf_V v_src = OK v_tgt):
    globdef_sim defs_src defs_tgt (Gvar v_src) (Gvar v_tgt)
.

Definition globdefs_sim
           (defs_src:PTree.t (globdef Fundef_src V_src))
           (defs_tgt:PTree.t (globdef Fundef_tgt V_tgt)):
  Prop :=
  forall i,
    match PTree.get i defs_src, PTree.get i defs_tgt with
      | Some g1, Some g2 => globdef_sim defs_src defs_tgt g1 g2
      | None, None => True
      | _, _ => False
    end.

Definition globdef_list_sim
           (defs_src:list (positive * globdef Fundef_src V_src))
           (defs_tgt:list (positive * globdef Fundef_tgt V_tgt)):
  Prop :=
  list_forall2
    (fun g_src g_tgt =>
       fst g_src = fst g_tgt /\
       globdef_sim
         (PTree.unelements defs_src)
         (PTree.unelements defs_tgt)
         (snd g_src) (snd g_tgt))
    defs_src defs_tgt.

Definition program_sim
           (p_src:program Fundef_src V_src)
           (p_tgt:program Fundef_tgt V_tgt): Prop :=
  globdef_list_sim p_src.(prog_defs) p_tgt.(prog_defs) /\
  p_src.(prog_main) = p_tgt.(prog_main).

Lemma globdefs_sim_globdef_list_sim
      (defs_src: PTree.t (globdef Fundef_src V_src))
      (defs_tgt: PTree.t (globdef Fundef_tgt V_tgt))
      (Hsim: globdefs_sim defs_src defs_tgt):
  globdef_list_sim (PTree.elements defs_src) (PTree.elements defs_tgt).
Proof.
  apply PTree.elements_canonical_order; intros.
  - exploit Hsim. instantiate (1 := i). rewrite H. intro X.
    destruct (defs_tgt ! i) eqn:Hi_tgt; [|inv X].
    eexists. split; eauto.
    admit. (* TODO: PTree.elements, PTree.unelements *)
  - exploit Hsim. instantiate (1 := i). rewrite H. intro X.
    destruct (defs_src ! i) eqn:Hi_src; [|inv X].
    eexists. split; eauto.
    admit. (* TODO: PTree.elements, PTree.unelements *)
Qed.

Lemma globdef_list_sim_globdefs_sim
      (defs_src: list (positive * globdef Fundef_src V_src))
      (defs_tgt: list (positive * globdef Fundef_tgt V_tgt))
      (Hsim: globdef_list_sim defs_src defs_tgt):
  globdefs_sim (PTree.unelements defs_src) (PTree.unelements defs_tgt).
Proof.
  unfold globdefs_sim, globdef_list_sim in *.
  revert Hsim.
  generalize (PTree.unelements defs_tgt) at 1 3 as defs_tgt'.
  generalize (PTree.unelements defs_src) at 1 3 as defs_src'.
  intros defs_src' defs_tgt' Hsim.
  unfold PTree.unelements. rewrite <- ? fold_left_rev_right.
  apply list_forall2_rev in Hsim. revert Hsim.
  generalize (rev defs_src) (rev defs_tgt).
  clear defs_src defs_tgt.
  induction l; intros l2 H; inv H; simpl.
  { intro. rewrite ? PTree.gempty. auto. }
  destruct H2, a, b1. simpl in *. subst.
  intro. rewrite ? PTree.gsspec. destruct (peq i p0); subst; auto.
  apply IHl. auto.
Qed.


(** properties of linking on simulation *)
Ltac simplify_decs :=
  repeat
    match goal with
      | [Hl: fundef_src_dec ?f = _,
         Hr: fundef_src_dec ?f = _ |- _] =>
        rewrite Hl in Hr; inv Hr
      | [Hl: fundef_tgt_dec ?f = _,
         Hr: fundef_tgt_dec ?f = _ |- _] =>
        rewrite Hl in Hr; inv Hr
      | [Hl: transf_EF ?ef = _,
         Hr: transf_EF ?ef = _ |- _] =>
        rewrite Hl in Hr; inv Hr
    end.

Lemma link_globdefs_sim
      (defs1_src defs2_src:PTree.t (globdef Fundef_src V_src))
      (defs1_tgt defs2_tgt:PTree.t (globdef Fundef_tgt V_tgt))
      defs_src (Hdefs_src: link_globdefs fundef_src_dec EF_src_dec V_src_dec defs1_src defs2_src = Some defs_src)
      (H1: globdefs_sim defs1_src defs1_tgt)
      (H2: globdefs_sim defs2_src defs2_tgt):
  exists defs_tgt,
    link_globdefs fundef_tgt_dec EF_tgt_dec V_tgt_dec defs1_tgt defs2_tgt = Some defs_tgt /\
    globdefs_sim defs_src defs_tgt.
Proof.
  generalize (link_globdefs_linkeq_l _ _ _ _ _ Hdefs_src). intro Hle1_src.
  generalize (link_globdefs_linkeq_r _ _ _ _ _ Hdefs_src). intro Hle2_src.
  destruct (link_globdefs fundef_tgt_dec EF_tgt_dec V_tgt_dec defs1_tgt defs2_tgt) eqn:Hdefs_tgt.
  { generalize (link_globdefs_linkeq_l _ _ _ _ _ Hdefs_tgt). intro Hle1_tgt.
    generalize (link_globdefs_linkeq_r _ _ _ _ _ Hdefs_tgt). intro Hle2_tgt.
    eexists. split; [eauto|].
    intro i. rename t into defs_tgt.
    eapply gtlink_globdefs in Hdefs_src. instantiate (1 := i) in Hdefs_src.
    eapply gtlink_globdefs in Hdefs_tgt. instantiate (1 := i) in Hdefs_tgt.
    specialize (H1 i). specialize (H2 i).
    destruct (defs1_src ! i) eqn:Hi1_src, (defs2_src ! i) eqn:Hi2_src, (defs_src ! i) eqn:Hi_src; subst; try (inv Hdefs_src; fail);
    destruct (defs1_tgt ! i) eqn:Hi1_tgt, (defs2_tgt ! i) eqn:Hi2_tgt, (defs_tgt ! i) eqn:Hi_tgt; subst; try (inv Hdefs_tgt; fail);
    try (inv H1; fail); try (inv H2; fail); auto.
    { destruct Hdefs_src as [[]|[]], Hdefs_tgt as [[]|[]]; subst; auto.
      { inv H; inv H1; inv H2; inv H3; inv Hv; inv Hv0; try inv Hf; try inv Hf0; simplify_decs.
        { repeat constructor. eapply globfun_sim_i; eauto.
          intros. apply Hsim; etransitivity; eauto.
        }
        { repeat constructor. eapply globfun_sim_e; eauto. }
        { constructor. destruct v1, v2. simpl in *. subst.
          unfold transf_globvar in *. simpl in *.
          destruct (transf_V gvar_info0); inv H0. simpl in *.
          inv Hv1. inv Hv2. simpl in *. subst. auto.
        }
      }
      { inv H; inv H1; inv H2; inv H3; inv Hv; inv Hv0; try inv Hf; try inv Hf0; simplify_decs.
        { repeat constructor. eapply globfun_sim_e; eauto. }
        { constructor. destruct v1, v2. simpl in *. subst.
          unfold transf_globvar in *. simpl in *.
          destruct (transf_V gvar_info0); inv H0. simpl in *.
          inv Hv1. inv Hv2. simpl in *. subst. auto.
        }
      }
      { admit. (* TODO *) }
      { admit. (* TODO *) }
    }
    { inv H1; constructor; auto.
      inv Hf; [eapply globfun_sim_i|eapply globfun_sim_e]; eauto.
      intros. apply Hsim; etransitivity; eauto.
    }
    { inv H2; constructor; auto.
      inv Hf; [eapply globfun_sim_i|eapply globfun_sim_e]; eauto.
      intros. apply Hsim; etransitivity; eauto.
    }
  }
  { apply gflink_globdefs in Hdefs_tgt.
    destruct Hdefs_tgt as [i [def1 [def2 [Hdef1 [Hdef2 [H12 H21]]]]]].
    specialize (H1 i). rewrite Hdef1 in H1.
    destruct (defs1_src ! i) eqn:Hi1_src; [|inv H1].
    specialize (H2 i). rewrite Hdef2 in H2.
    destruct (defs2_src ! i) eqn:Hi2_src; [|inv H2].
    eapply gtlink_globdefs in Hdefs_src.
    instantiate (1 := i) in Hdefs_src.
    rewrite Hi1_src, Hi2_src in Hdefs_src.
    destruct (defs_src ! i) eqn:Hi_src; [|inv Hdefs_src].
    destruct Hdefs_src as [[]|[]]; subst.
    { inv H1; inv H2; inv H; inv Hv; try inv Hv0; try inv Hf; try inv Hf0; simplify_decs.
      { contradict H12. constructor. eapply globfun_linkable_ei; eauto. }
      { contradict H12. constructor. eapply globfun_linkable_ee; eauto. }
      { contradict H12. constructor.
        destruct v_src, v_src0. inv Hv1. simpl in *. subst.
        unfold transf_globvar in *. simpl in *.
        destruct (transf_V gvar_info0); inv H0; inv H1.
        constructor; auto.
      }
    }
    { inv H1; inv H2; inv H; inv Hv; try inv Hv0; try inv Hf; try inv Hf0; simplify_decs.
      { contradict H21. constructor. eapply globfun_linkable_ei; eauto. }
      { contradict H21. constructor. eapply globfun_linkable_ee; eauto. }
      { contradict H21. constructor.
        destruct v_src, v_src0. inv Hv1. simpl in *. subst.
        unfold transf_globvar in *. simpl in *.
        destruct (transf_V gvar_info); inv H0; inv H1.
        constructor; auto.
      }
    }
  }
Qed.

Lemma link_globdef_list_sim
      (defs1_src defs2_src:list (positive * globdef Fundef_src V_src))
      (defs1_tgt defs2_tgt:list (positive * globdef Fundef_tgt V_tgt))
      defs_src (Hdefs_src: link_globdef_list fundef_src_dec EF_src_dec V_src_dec defs1_src defs2_src = Some defs_src)
      (H1: globdef_list_sim defs1_src defs1_tgt)
      (H2: globdef_list_sim defs2_src defs2_tgt):
  exists defs_tgt,
    link_globdef_list fundef_tgt_dec EF_tgt_dec V_tgt_dec defs1_tgt defs2_tgt = Some defs_tgt /\
    globdef_list_sim defs_src defs_tgt.
Proof.
  apply globdef_list_sim_globdefs_sim in H1.
  apply globdef_list_sim_globdefs_sim in H2.
  unfold link_globdef_list in Hdefs_src.
  match goal with
    | [H: context[link_globdefs ?fundef_dec ?EF_dec ?V_dec ?defs1 ?defs2] |- _] =>
      destruct (link_globdefs fundef_dec EF_dec V_dec defs1 defs2) as [defs|] eqn:Hdefs; inv H
  end.
  exploit link_globdefs_sim; eauto. intros [defs_tgt [Hdefs_tgt Hsim]].
  unfold link_globdef_list. rewrite Hdefs_tgt. eexists. split; eauto.
  apply globdefs_sim_globdef_list_sim. auto.
Qed.

Lemma link_program_sim
      (p1_src p2_src:program Fundef_src V_src)
      (p1_tgt p2_tgt:program Fundef_tgt V_tgt)
      p_src (Hm_src: link_program fundef_src_dec EF_src_dec V_src_dec p1_src p2_src = Some p_src)
      (H1: program_sim p1_src p1_tgt)
      (H2: program_sim p2_src p2_tgt):
  exists m_tgt,
    link_program fundef_tgt_dec EF_tgt_dec V_tgt_dec p1_tgt p2_tgt = Some m_tgt /\
    program_sim p_src m_tgt.
Proof.
  destruct p1_src as [defs1_src main1_src].
  destruct p1_tgt as [defs1_tgt main1_tgt].
  destruct p2_src as [defs2_src main2_src].
  destruct p2_tgt as [defs2_tgt main2_tgt].
  destruct H1 as [H1d H1m], H2 as [H2d H2m].
  unfold link_program in *. simpl in *. subst.
  destruct ((main1_tgt =? main2_tgt)%positive) eqn:Hmain; [|inv Hm_src].
  apply Pos.eqb_eq in Hmain. subst.
  destruct (link_globdef_list fundef_src_dec EF_src_dec V_src_dec defs1_src defs2_src) as [defs_src|] eqn:Hdef_src; inv Hm_src.
  exploit link_globdef_list_sim; eauto.
  intros [defs_tgt [Hdefs_tgt Hsim]].
  rewrite Hdefs_tgt. eexists. split; eauto.
  split; auto.
Qed.

Section INITIALIZE.

Variable (p_src: program Fundef_src V_src).
Variable (p_tgt: program Fundef_tgt V_tgt).
Variable (Hp: program_sim p_src p_tgt).

Definition match_fundef :=
  globfun_sim
    (PTree.unelements p_src.(prog_defs))
    (PTree.unelements p_tgt.(prog_defs)).

Lemma program_sim_match_program:
  match_program match_fundef V_sim nil p_src.(prog_main) p_src p_tgt.
Proof.
  destruct Hp as [Hdefs Hmain].
  unfold match_program. split; eauto.
  exists p_tgt.(prog_defs). split; [|rewrite app_nil_r; auto].
  eapply list_forall2_imply; eauto. intros.
  destruct H1 as [H1 H2].
  destruct v1 as [var1 g1], v2 as [var2 g2]. simpl in *. subst.
  inv H2.
  - constructor. auto.
  - destruct v_src. unfold transf_globvar in Hv. simpl in Hv.
    destruct (transf_V gvar_info) eqn:Hinfo; inv Hv. simpl in *.
    constructor. auto.
Qed.

Lemma globalenvs_match:
  Genv.match_genvs match_fundef V_sim nil (Genv.globalenv p_src) (Genv.globalenv p_tgt).
Proof.
  generalize program_sim_match_program. intro Hmatch.
  eapply Genv.globalenvs_match; eauto; auto.
Qed.

Lemma program_sim_init_mem_match:
  forall m,
    Genv.init_mem p_src = Some m ->
    Genv.init_mem p_tgt = Some m.
Proof.
  generalize program_sim_match_program. intro Hmatch.
  intros. erewrite Genv.init_mem_match; eauto; auto.
Qed.

Theorem find_symbol_match:
  forall (s : ident),
  Genv.find_symbol (Genv.globalenv p_tgt) s = Genv.find_symbol (Genv.globalenv p_src) s.
Proof.
  generalize program_sim_match_program. intros Hmatch s.
  eapply Genv.find_symbol_match; eauto.
Qed.

Theorem find_funct_ptr_match:
  forall (b : block) (f : Fundef_src),
  Genv.find_funct_ptr (Genv.globalenv p_src) b = Some f ->
  exists tf : Fundef_tgt,
  Genv.find_funct_ptr (Genv.globalenv p_tgt) b = Some tf /\ match_fundef f tf.
Proof.
  generalize program_sim_match_program. intros Hmatch b f Hf.
  eapply Genv.find_funct_ptr_match; eauto.
Qed.

End INITIALIZE.

End PROGRAM_SIM.
