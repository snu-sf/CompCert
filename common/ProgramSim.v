Require Import RelationClasses.
Require String.
Require Import Coqlib Coqlib_linker.
Require Import Maps_linker.
Require Import Integers Floats Values AST Globalenvs.
Require Import LinkerSpecification LinkerProp Linkeq.
Require Import Errors.
Require Import paco.

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

Definition F_simT :=
  forall
    (defs_src:list (positive * globdef Fundef_src V_src))
    (defs_tgt:list (positive * globdef Fundef_tgt V_tgt))
    (f_src:F_src) (f_tgt:F_tgt), Prop.

Section CORE.

Variable (F_sim:F_simT).
Variable (defs_src:list (positive * globdef Fundef_src V_src)).
Variable (defs_tgt:list (positive * globdef Fundef_tgt V_tgt)).

Inductive globvar_sim (v_src:globvar V_src) (v_tgt:globvar V_tgt): Prop :=
| globvar_sim_intro
    (Hv: transf_globvar transf_V v_src = OK v_tgt)
.

(** simulation *)
Inductive globfun_sim
          (g_src:Fundef_src) (g_tgt:Fundef_tgt): Prop :=
| globfun_sim_i
    f_src f_tgt
    (Hsrc: fundef_src_dec g_src = inl f_src)
    (Htgt: fundef_tgt_dec g_tgt = inl f_tgt)
    (Hsim: forall fdefs_src fdefs_tgt
                  (Hfdefs_src: globdef_list_linkeq fundef_src_dec defs_src fdefs_src)
                  (Hfdefs_tgt: globdef_list_linkeq fundef_tgt_dec defs_tgt fdefs_tgt),
             F_sim fdefs_src fdefs_tgt f_src f_tgt)
| globfun_sim_e
    ef_src ef_tgt (Hef: transf_EF ef_src = OK ef_tgt)
    (Hsrc: fundef_src_dec g_src = inr ef_src)
    (Htgt: fundef_tgt_dec g_tgt = inr ef_tgt)
.

Inductive globdef_sim:
  forall (g_src:globdef Fundef_src V_src) (g_tgt:globdef Fundef_tgt V_tgt), Prop :=
| globdef_sim_fun
    f_src f_tgt (Hf: globfun_sim f_src f_tgt):
    globdef_sim (Gfun f_src) (Gfun f_tgt)
| globdef_sim_var
    v_src v_tgt (Hv: globvar_sim v_src v_tgt):
    globdef_sim (Gvar v_src) (Gvar v_tgt)
.

Definition globdefs_sim
           (ds_src:PTree.t (globdef Fundef_src V_src))
           (ds_tgt:PTree.t (globdef Fundef_tgt V_tgt)): Prop :=
  forall i,
    match PTree.get i ds_src, PTree.get i ds_tgt with
      | Some g1, Some g2 => globdef_sim g1 g2
      | None, None => True
      | _, _ => False
    end.

Definition globdef_list_sim
           (ds_src:list (positive * globdef Fundef_src V_src))
           (ds_tgt:list (positive * globdef Fundef_tgt V_tgt)): Prop :=
  list_forall2
    (fun g_src g_tgt =>
       fst g_src = fst g_tgt /\
       globdef_sim (snd g_src) (snd g_tgt))
    ds_src ds_tgt.

End CORE.

(** properties on F_sim and simulation *)
Lemma globfun_sim_le
      (F_sim1 F_sim2:F_simT)
      (defs1_src defs2_src:list (positive * globdef Fundef_src V_src))
      (defs1_tgt defs2_tgt:list (positive * globdef Fundef_tgt V_tgt))
      (HF_sim: F_sim1 <4= F_sim2)
      (Hdefs_src: globdef_list_linkeq fundef_src_dec defs1_src defs2_src)
      (Hdefs_tgt: globdef_list_linkeq fundef_tgt_dec defs1_tgt defs2_tgt):
  (globfun_sim F_sim1 defs1_src defs1_tgt) <2= (globfun_sim F_sim2 defs2_src defs2_tgt).
Proof.
  intros. inv PR.
  - eapply globfun_sim_i; eauto.
    intros. apply HF_sim. eapply Hsim.
    + rewrite Hdefs_src. auto.
    + rewrite Hdefs_tgt. auto.
  - eapply globfun_sim_e; eauto.
Qed.

Lemma globdef_sim_le
      (F_sim1 F_sim2:F_simT)
      (defs1_src defs2_src:list (positive * globdef Fundef_src V_src))
      (defs1_tgt defs2_tgt:list (positive * globdef Fundef_tgt V_tgt))
      (HF_sim: F_sim1 <4= F_sim2)
      (Hdefs_src: globdef_list_linkeq fundef_src_dec defs1_src defs2_src)
      (Hdefs_tgt: globdef_list_linkeq fundef_tgt_dec defs1_tgt defs2_tgt):
  (globdef_sim F_sim1 defs1_src defs1_tgt) <2= (globdef_sim F_sim2 defs2_src defs2_tgt).
Proof.
  intros. inv PR.
  - eapply globdef_sim_fun; eauto.
    eapply globfun_sim_le; eauto.
  - eapply globdef_sim_var; eauto.
Qed.

Lemma globdef_list_sim_le
      (F_sim1 F_sim2:F_simT)
      (defs1_src defs2_src:list (positive * globdef Fundef_src V_src))
      (defs1_tgt defs2_tgt:list (positive * globdef Fundef_tgt V_tgt))
      (HF_sim: F_sim1 <4= F_sim2)
      (Hdefs_src: globdef_list_linkeq fundef_src_dec defs1_src defs2_src)
      (Hdefs_tgt: globdef_list_linkeq fundef_tgt_dec defs1_tgt defs2_tgt):
  (globdef_list_sim F_sim1 defs1_src defs1_tgt) <2= (globdef_list_sim F_sim2 defs2_src defs2_tgt).
Proof.
  intros.
  eapply list_forall2_imply; eauto. simpl. intros.
  destruct H1, v1, v2. simpl in *. subst.
  split; auto. eapply globdef_sim_le; eauto.
Qed.

(** globdefs_sim and globdef_list_sim *)

Lemma globdefs_sim_globdef_list_sim
      (F_sim:F_simT)
      (defs_src:list (positive * globdef Fundef_src V_src))
      (defs_tgt:list (positive * globdef Fundef_tgt V_tgt))
      (ds_src: PTree.t (globdef Fundef_src V_src))
      (ds_tgt: PTree.t (globdef Fundef_tgt V_tgt))
      (Hsim: globdefs_sim F_sim defs_src defs_tgt ds_src ds_tgt):
  globdef_list_sim F_sim defs_src defs_tgt (PTree.elements ds_src) (PTree.elements ds_tgt).
Proof.
  apply PTree.elements_canonical_order; intros.
  - exploit Hsim. instantiate (1 := i). rewrite H. intro X.
    destruct (ds_tgt ! i) eqn:Hi_tgt; [|inv X].
    eexists. split; eauto.
  - exploit Hsim. instantiate (1 := i). rewrite H. intro X.
    destruct (ds_src ! i) eqn:Hi_src; [|inv X].
    eexists. split; eauto.
Qed.

Lemma globdef_list_sim_globdefs_sim
      (F_sim:F_simT)
      (defs_src:list (positive * globdef Fundef_src V_src))
      (defs_tgt:list (positive * globdef Fundef_tgt V_tgt))
      (ds_src:list (positive * globdef Fundef_src V_src))
      (ds_tgt:list (positive * globdef Fundef_tgt V_tgt))
      (Hsim: globdef_list_sim F_sim defs_src defs_tgt ds_src ds_tgt):
  globdefs_sim F_sim defs_src defs_tgt (PTree.unelements ds_src) (PTree.unelements ds_tgt).
Proof.
  unfold globdefs_sim, globdef_list_sim in *. revert ds_tgt Hsim.
  induction ds_src; intros ds_tgt Hsim i; inv Hsim; simpl; auto.
  { rewrite ? PTree.gempty. auto. }
  destruct a, b1, H1. simpl in *. subst.
  rewrite ? PTree.gsspec. destruct (peq i p0); simpl; subst; auto.
  apply IHds_src. auto.
Qed.

(** an instantiation of weak simulation: matching any function definitions *)
Definition globdef_list_weak_sim := globdef_list_sim (fun _ _ _ _ => True) nil nil.

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
      (F_sim:F_simT)
      (defs1_src defs2_src:list (positive * globdef Fundef_src V_src))
      (defs1_tgt defs2_tgt:list (positive * globdef Fundef_tgt V_tgt))
      defs_src (Hdefs_src: link_globdefs fundef_src_dec EF_src_dec V_src_dec (PTree.unelements defs1_src) (PTree.unelements defs2_src) = Some defs_src)
      (H1: globdefs_sim F_sim defs1_src defs1_tgt (PTree.unelements defs1_src) (PTree.unelements defs1_tgt))
      (H2: globdefs_sim F_sim defs2_src defs2_tgt (PTree.unelements defs2_src) (PTree.unelements defs2_tgt)):
  exists defs_tgt,
    link_globdefs fundef_tgt_dec EF_tgt_dec V_tgt_dec (PTree.unelements defs1_tgt) (PTree.unelements defs2_tgt) = Some defs_tgt /\
    globdefs_sim F_sim (PTree.elements defs_src) (PTree.elements defs_tgt) defs_src defs_tgt.
Proof.
  destruct (link_globdefs fundef_tgt_dec EF_tgt_dec V_tgt_dec (PTree.unelements defs1_tgt) (PTree.unelements defs2_tgt)) as [defs_tgt|] eqn:Hdefs_tgt.
  { eexists. split; [eauto|].
    intro i. 
    eapply gtlink_globdefs in Hdefs_src. instantiate (1 := i) in Hdefs_src.
    eapply gtlink_globdefs in Hdefs_tgt. instantiate (1 := i) in Hdefs_tgt.
    specialize (H1 i). specialize (H2 i).
    destruct ((PTree.unelements defs1_src) ! i) eqn:Hi1_src,
             ((PTree.unelements defs2_src) ! i) eqn:Hi2_src,
             (defs_src ! i) eqn:Hi_src; subst; try (inv Hdefs_src; fail);
    destruct ((PTree.unelements defs1_tgt) ! i) eqn:Hi1_tgt,
             ((PTree.unelements defs2_tgt) ! i) eqn:Hi2_tgt,
             (defs_tgt ! i) eqn:Hi_tgt; subst; try (inv Hdefs_tgt; fail);
    try (inv H1; fail); try (inv H2; fail); auto.
    admit.
    admit.
    admit.
  }
  { apply gflink_globdefs in Hdefs_tgt.
    destruct Hdefs_tgt as [i [def1 [def2 [Hdef1 [Hdef2 [H12 H21]]]]]].
    specialize (H1 i). rewrite Hdef1 in H1.
    destruct ((PTree.unelements defs1_src) ! i) eqn:Hi1_src; [|inv H1].
    specialize (H2 i). rewrite Hdef2 in H2.
    destruct ((PTree.unelements defs2_src) ! i) eqn:Hi2_src; [|inv H2].
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
        destruct (transf_V gvar_info0); inv Hv; inv Hv2; simpl in *; subst.
        constructor; auto.
      }
    }
    { inv H1; inv H2; inv H; inv Hv; try inv Hv0; try inv Hf; try inv Hf0; simplify_decs.
      { contradict H21. constructor. eapply globfun_linkable_ei; eauto. }
      { contradict H21. constructor. eapply globfun_linkable_ee; eauto. }
      { contradict H21. constructor.
        destruct v_src, v_src0. inv Hv1. simpl in *. subst.
        unfold transf_globvar in *. simpl in *.
        destruct (transf_V gvar_info); inv Hv; inv Hv2; simpl in *; subst.
        constructor; auto.
      }
    }
  }
Qed.

Lemma link_globdef_list_sim_aux
      (F_sim:F_simT)
      (defs1_src defs2_src:list (positive * globdef Fundef_src V_src))
      (defs1_tgt defs2_tgt:list (positive * globdef Fundef_tgt V_tgt))
      defs_src (Hdefs_src: link_globdef_list fundef_src_dec EF_src_dec V_src_dec defs1_src defs2_src = Some defs_src)
      (H1: globdef_list_sim F_sim defs1_src defs1_tgt defs1_src defs1_tgt)
      (H2: globdef_list_sim F_sim defs2_src defs2_tgt defs2_src defs2_tgt):
  exists defs_tgt,
    link_globdef_list fundef_tgt_dec EF_tgt_dec V_tgt_dec defs1_tgt defs2_tgt = Some defs_tgt /\
    globdef_list_sim F_sim defs_src defs_tgt defs_src defs_tgt.
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

Lemma link_globdef_list_sim
      (F_sim:F_simT)
      (defs1_src defs2_src:list (positive * globdef Fundef_src V_src))
      (defs1_tgt defs2_tgt:list (positive * globdef Fundef_tgt V_tgt))
      defs_src (Hdefs_src: link_globdef_list fundef_src_dec EF_src_dec V_src_dec defs1_src defs2_src = Some defs_src)
      (H1: globdef_list_sim F_sim defs1_src defs1_tgt defs1_src defs1_tgt)
      (H2: globdef_list_sim F_sim defs2_src defs2_tgt defs2_src defs2_tgt):
  exists defs_tgt,
    link_globdef_list fundef_tgt_dec EF_tgt_dec V_tgt_dec defs1_tgt defs2_tgt = Some defs_tgt /\
    globdef_list_sim F_sim defs_src defs_tgt defs_src defs_tgt.
Proof.
  generalize (link_globdef_list_linkeq_l _ _ _ _ _ Hdefs_src). intro Hle1_src.
  generalize (link_globdef_list_linkeq_r _ _ _ _ _ Hdefs_src). intro Hle2_src.
  exploit link_globdef_list_sim_aux; eauto.
Qed.

Section DEF.

Variable (F_sim:F_simT).

Definition F_sim_weak_sim :=
  fun defs_src defs_tgt f_src f_tgt =>
    forall (Hdefs: globdef_list_weak_sim defs_src defs_tgt),
    F_sim defs_src defs_tgt f_src f_tgt.

Definition program_sim
           (p_src: program Fundef_src V_src)
           (p_tgt: program Fundef_tgt V_tgt): Prop :=
  globdef_list_sim F_sim_weak_sim p_src.(prog_defs) p_tgt.(prog_defs) p_src.(prog_defs) p_tgt.(prog_defs) /\
  p_src.(prog_main) = p_tgt.(prog_main).

Lemma link_program_sim
      (p1_src p2_src:program Fundef_src V_src)
      (p1_tgt p2_tgt:program Fundef_tgt V_tgt)
      p_src (Hp_src: link_program fundef_src_dec EF_src_dec V_src_dec p1_src p2_src = Some p_src)
      (H1: program_sim p1_src p1_tgt)
      (H2: program_sim p2_src p2_tgt):
  exists p_tgt,
    link_program fundef_tgt_dec EF_tgt_dec V_tgt_dec p1_tgt p2_tgt = Some p_tgt /\
    program_sim p_src p_tgt.
Proof.
  destruct p1_src as [defs1_src main1_src].
  destruct p1_tgt as [defs1_tgt main1_tgt].
  destruct p2_src as [defs2_src main2_src].
  destruct p2_tgt as [defs2_tgt main2_tgt].
  destruct H1 as [H1d H1m], H2 as [H2d H2m].
  unfold link_program in *. simpl in *. subst.
  destruct ((main1_tgt =? main2_tgt)%positive) eqn:Hmain; [|inv Hp_src].
  apply Pos.eqb_eq in Hmain. subst.
  destruct (link_globdef_list fundef_src_dec EF_src_dec V_src_dec defs1_src defs2_src) as [def_list_src|] eqn:Hdef_list_src; inv Hp_src.
  exploit link_globdef_list_sim; eauto. intros [defs_tgt [Hdefs_tgt Hsim]].
  exists (mkprogram defs_tgt main2_tgt). rewrite Hdefs_tgt. split; auto.
  constructor; auto.
Qed.

End DEF.

Lemma program_sim_le
      (F_sim1 F_sim2:F_simT) (HF_sim: F_sim1 <4= F_sim2):
  (program_sim F_sim1) <2= (program_sim F_sim2).
Proof.
  intros. destruct PR as [Hdefs Hmain]. split; auto.
  eapply globdef_list_sim_le; eauto.
  - reflexivity.
  - reflexivity.
  - eapply list_forall2_imply; eauto. intros. simpl in *.
    destruct v1, v2, H1. simpl in *. subst.
    split; auto.
    eapply globdef_sim_le; try reflexivity; [|eauto].
    intros. repeat intro. specialize (PR Hdefs0). auto.
Qed.

Inductive fundef_weak_sim (ge_src:Genv.t Fundef_src V_src) (ge_tgt:Genv.t Fundef_tgt V_tgt) (f_src:Fundef_src) (f_tgt:Fundef_tgt): Prop :=
| fundef_weak_sim_intro
    b
    (Hsrc: Maps.PTree.get b ge_src.(Genv.genv_funs) = Some f_src)
    (Htgt: Maps.PTree.get b ge_tgt.(Genv.genv_funs) = Some f_tgt)
.

Section INITIALIZE.

Variable (p_src: program Fundef_src V_src).
Variable (p_tgt: program Fundef_tgt V_tgt).
Variable (Hdefs: globdef_list_weak_sim p_src.(prog_defs) p_tgt.(prog_defs)).
Variable (Hmain: p_src.(prog_main) = p_tgt.(prog_main)).

Let ge_src := Genv.globalenv p_src.
Let ge_tgt := Genv.globalenv p_tgt.

Lemma program_sim_match_program:
  match_program (fundef_weak_sim ge_src ge_tgt) V_sim nil p_src.(prog_main) p_src p_tgt.
Proof.
  unfold match_program. split; eauto.
  exists p_tgt.(prog_defs). split; [|rewrite app_nil_r; auto].
  revert Hdefs.
  generalize (prog_defs p_src) as l1, (prog_defs p_tgt) as l2.
  induction l1; intros l2 Hsim; inv Hsim; constructor; auto.
  destruct a, b1, H1. simpl in *. subst.
  inv H0.
  - admit.
  - destruct v_src, v_tgt. inv Hv. unfold transf_globvar in Hv0. simpl in *.
    destruct (transf_V gvar_info) eqn:Hgvar_info; inv Hv0. constructor; auto.
Qed.
Local Hint Resolve program_sim_match_program.

Lemma globalenvs_match:
  Genv.match_genvs (fundef_weak_sim ge_src ge_tgt) V_sim nil (Genv.globalenv p_src) (Genv.globalenv p_tgt).
Proof.
  eapply Genv.globalenvs_match; eauto.
Qed.
Local Hint Resolve globalenvs_match.

Lemma program_sim_init_mem_match:
  forall m,
    Genv.init_mem p_src = Some m ->
    Genv.init_mem p_tgt = Some m.
Proof.
  intros. erewrite Genv.init_mem_match; eauto; auto.
Qed.

Lemma symbols_preserved:
  forall (s : ident),
  Genv.find_symbol (Genv.globalenv p_tgt) s = Genv.find_symbol (Genv.globalenv p_src) s.
Proof.
  intros. eapply Genv.find_symbol_match; eauto.
Qed.

Lemma varinfo_preserved:
  forall b,
    match Genv.find_var_info (Genv.globalenv p_tgt) b, Genv.find_var_info (Genv.globalenv p_src) b with
      | None, None => True
      | Some v_tgt, Some v_src =>
        transf_globvar transf_V v_src = OK v_tgt
      | _, _ => False
    end.
Proof.
  intros. case_eq (Genv.find_var_info (Genv.globalenv p_src) b); intros.
  - exploit Genv.find_var_info_match; eauto. intros [tv [Htv Hsim]].
    rewrite Htv. inv Hsim. inv H0.
    unfold transf_globvar, bind. simpl in *. rewrite H2. auto.
  - case_eq (Genv.find_var_info (Genv.globalenv p_tgt) b); intros; auto.
    exploit Genv.find_var_info_rev_match; eauto.
    destruct (plt b (Genv.genv_next (Genv.globalenv p_src))); [|intro X; inv X].
    intros [v [Hv Hsim]]. rewrite H in Hv. inv Hv.
Qed.

Lemma functions_translated:
  forall v f,
  Genv.find_funct (Genv.globalenv p_src) v = Some f ->
  exists tf, Genv.find_funct (Genv.globalenv p_tgt) v = Some tf /\ fundef_weak_sim ge_src ge_tgt f tf.
Proof.
  intros. eapply Genv.find_funct_match; eauto.
Qed.

Lemma funct_ptr_translated:
  forall (b : block) (f : Fundef_src),
  Genv.find_funct_ptr (Genv.globalenv p_src) b = Some f ->
  exists tf : Fundef_tgt,
  Genv.find_funct_ptr (Genv.globalenv p_tgt) b = Some tf /\ fundef_weak_sim ge_src ge_tgt f tf.
Proof.
  intros. eapply Genv.find_funct_ptr_match; eauto.
Qed.

End INITIALIZE.

End PROGRAM_SIM.
