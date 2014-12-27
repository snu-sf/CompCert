Require Import RelationClasses.
Require String.
Require Import Coqlib Coqlib_linker.
Require Import Maps_linker.
Require Import Integers Floats Values AST Globalenvs.
Require Import LinkerSpecification LinkerProp Linkeq.
Require Import Errors.
Require Import paco.

Set Implicit Arguments.

(* external function prservation function *)
Lemma external_function_OK_sig:
  forall ef1 ef2, (OK ef1 = OK ef2) -> ef_sig ef1 = ef_sig ef2.
Proof.
  intros. inv H. auto.
Qed.

(* lifting function simulation to program simulation *)
Section PROGRAM_LSIM.

Variable (fundefT_src F_src V_src:Type).
Variable (fundef_src_dec: fundef_decT fundefT_src F_src).
Variable (V_src_dec: forall (v1 v2:V_src), {v1 = v2} + {v1 <> v2}).
Variable (F_sig_src: forall (f:F_src), signature).
Let fundef_sig_src (fundef:fundefT_src): signature :=
  match fundef_src_dec fundef with
    | inl f => F_sig_src f
    | inr ef => ef_sig ef
  end.

Variable (fundefT_tgt F_tgt V_tgt:Type).
Variable (fundef_tgt_dec: fundef_decT fundefT_tgt F_tgt).
Variable (V_tgt_dec: forall (v1 v2:V_tgt), {v1 = v2} + {v1 <> v2}).
Variable (F_sig_tgt: forall (f:F_tgt), signature).
Let fundef_sig_tgt (fundef:fundefT_tgt): signature :=
  match fundef_tgt_dec fundef with
    | inl f => F_sig_tgt f
    | inr ef => ef_sig ef
  end.

Variable (transf_V: forall (v:V_src), res V_tgt).
Let V_lsim (v_src:V_src) (v_tgt:V_tgt) := transf_V v_src = OK v_tgt.

Definition F_lsimT :=
  forall
    (fprog_src:program fundefT_src V_src)
    (fprog_tgt:program fundefT_tgt V_tgt)
    (f_src:F_src) (f_tgt:F_tgt), Prop.

Section CORE.

Variable (F_lsim:F_lsimT).
Variable (prog_src:program fundefT_src V_src).
Variable (prog_tgt:program fundefT_tgt V_tgt).

Inductive globvar_lsim (v_src:globvar V_src) (v_tgt:globvar V_tgt): Prop :=
| globvar_lsim_intro
    (Hv: transf_globvar transf_V v_src = OK v_tgt)
.

(** simulation *)
Inductive globfun_lsim
          (g_src:fundefT_src) (g_tgt:fundefT_tgt): Prop :=
| globfun_lsim_i
    f_src f_tgt
    (Hsrc: fundef_src_dec g_src = inl f_src)
    (Htgt: fundef_tgt_dec g_tgt = inl f_tgt)
    (Hsim: forall fprog_src fprog_tgt
                  (Hfprog_src: program_linkeq fundef_src_dec prog_src fprog_src)
                  (Hfprog_tgt: program_linkeq fundef_tgt_dec prog_tgt fprog_tgt),
             F_lsim fprog_src fprog_tgt f_src f_tgt /\
             F_sig_src f_src = F_sig_tgt f_tgt)
| globfun_lsim_e
    ef
    (Hsrc: fundef_src_dec g_src = inr ef)
    (Htgt: fundef_tgt_dec g_tgt = inr ef)
.

Inductive globdef_lsim:
  forall (g_src:globdef fundefT_src V_src) (g_tgt:globdef fundefT_tgt V_tgt), Prop :=
| globdef_lsim_fun
    f_src f_tgt (Hf: globfun_lsim f_src f_tgt):
    globdef_lsim (Gfun f_src) (Gfun f_tgt)
| globdef_lsim_var
    v_src v_tgt (Hv: globvar_lsim v_src v_tgt):
    globdef_lsim (Gvar v_src) (Gvar v_tgt)
.

Definition globdefs_lsim
           (defs_src:PTree.t (globdef fundefT_src V_src))
           (defs_tgt:PTree.t (globdef fundefT_tgt V_tgt)): Prop :=
  forall i,
    match PTree.get i defs_src, PTree.get i defs_tgt with
      | Some g1, Some g2 => globdef_lsim g1 g2
      | None, None => True
      | _, _ => False
    end.

Definition globdef_list_lsim
           (defs_src:list (positive * globdef fundefT_src V_src))
           (defs_tgt:list (positive * globdef fundefT_tgt V_tgt)): Prop :=
  list_forall2
    (fun g_src g_tgt =>
       fst g_src = fst g_tgt /\
       globdef_lsim (snd g_src) (snd g_tgt))
    defs_src defs_tgt.

Definition program_lsim_aux: Prop :=
  globdef_list_lsim prog_src.(prog_defs) prog_tgt.(prog_defs) /\
  prog_src.(prog_main) = prog_tgt.(prog_main).

End CORE.

(** an instantiation of weak simulation: matching any function definitions *)
Definition program_weak_lsim := program_lsim_aux (fun _ _ _ _ => True).

(** properties on F_lsim and simulation *)
Lemma globfun_lsim_le
      (F_lsim1 F_lsim2:F_lsimT)
      (prog1_src prog2_src:program fundefT_src V_src)
      (prog1_tgt prog2_tgt:program fundefT_tgt V_tgt)
      (HF_lsim: F_lsim1 <4= F_lsim2)
      (Hprog_src: program_linkeq fundef_src_dec prog1_src prog2_src)
      (Hprog_tgt: program_linkeq fundef_tgt_dec prog1_tgt prog2_tgt):
  (globfun_lsim F_lsim1 prog1_src prog1_tgt) <2= (globfun_lsim F_lsim2 prog2_src prog2_tgt).
Proof.
  intros. inv PR.
  - eapply globfun_lsim_i; eauto.
    intros. exploit Hsim; eauto. intros [Hsim1 Hsig].
    split; auto. apply HF_lsim. eapply Hsim.
    + rewrite Hprog_src. auto.
    + rewrite Hprog_tgt. auto.
  - eapply globfun_lsim_e; eauto.
Qed.

Lemma globdef_lsim_le
      (F_lsim1 F_lsim2:F_lsimT)
      (prog1_src prog2_src:program fundefT_src V_src)
      (prog1_tgt prog2_tgt:program fundefT_tgt V_tgt)
      (HF_lsim: F_lsim1 <4= F_lsim2)
      (Hprog_src: program_linkeq fundef_src_dec prog1_src prog2_src)
      (Hprog_tgt: program_linkeq fundef_tgt_dec prog1_tgt prog2_tgt):
  (globdef_lsim F_lsim1 prog1_src prog1_tgt) <2= (globdef_lsim F_lsim2 prog2_src prog2_tgt).
Proof.
  intros. inv PR.
  - eapply globdef_lsim_fun; eauto.
    eapply globfun_lsim_le; eauto.
  - eapply globdef_lsim_var; eauto.
Qed.

Lemma globdef_list_lsim_le
      (F_lsim1 F_lsim2:F_lsimT)
      (prog1_src prog2_src:program fundefT_src V_src)
      (prog1_tgt prog2_tgt:program fundefT_tgt V_tgt)
      (HF_lsim: F_lsim1 <4= F_lsim2)
      (Hprog_src: program_linkeq fundef_src_dec prog1_src prog2_src)
      (Hprog_tgt: program_linkeq fundef_tgt_dec prog1_tgt prog2_tgt):
  (globdef_list_lsim F_lsim1 prog1_src prog1_tgt) <2= (globdef_list_lsim F_lsim2 prog2_src prog2_tgt).
Proof.
  intros.
  eapply list_forall2_imply; eauto. simpl. intros.
  destruct H1, v1, v2. simpl in *. subst.
  split; auto. eapply globdef_lsim_le; eauto.
Qed.

Lemma program_lsim_aux_le
      (F_lsim1 F_lsim2:F_lsimT)
      (HF_lsim: F_lsim1 <4= F_lsim2):
  (program_lsim_aux F_lsim1) <2= (program_lsim_aux F_lsim2).
Proof.
  intros prog_src prog_tgt Hsim.
  destruct prog_src as [defs_src main_src].
  destruct prog_tgt as [defs_tgt main_tgt].
  destruct Hsim as [Hdefs Hmain].
  simpl in *. subst. split; auto.
  eapply globdef_list_lsim_le; simpl; eauto.
  reflexivity. reflexivity.
Qed.

(** globdefs_lsim and globdef_list_lsim *)

Lemma globdefs_lsim_globdef_list_lsim
      (F_lsim:F_lsimT)
      (fprog_src:program fundefT_src V_src)
      (fprog_tgt:program fundefT_tgt V_tgt)
      (defs_src: PTree.t (globdef fundefT_src V_src))
      (defs_tgt: PTree.t (globdef fundefT_tgt V_tgt))
      (Hsim: globdefs_lsim F_lsim fprog_src fprog_tgt defs_src defs_tgt):
  globdef_list_lsim F_lsim fprog_src fprog_tgt (PTree.elements defs_src) (PTree.elements defs_tgt).
Proof.
  apply PTree.elements_canonical_order; intros.
  - exploit Hsim. instantiate (1 := i). rewrite H. intro X.
    destruct (defs_tgt ! i) eqn:Hi_tgt; [|inv X].
    eexists. split; eauto.
  - exploit Hsim. instantiate (1 := i). rewrite H. intro X.
    destruct (defs_src ! i) eqn:Hi_src; [|inv X].
    eexists. split; eauto.
Qed.

Lemma globdef_list_lsim_globdefs_lsim
      (F_lsim:F_lsimT)
      (fprog_src:program fundefT_src V_src)
      (fprog_tgt:program fundefT_tgt V_tgt)
      (defs_src: list (positive * (globdef fundefT_src V_src)))
      (defs_tgt: list (positive * (globdef fundefT_tgt V_tgt)))
      (Hsim: globdef_list_lsim F_lsim fprog_src fprog_tgt defs_src defs_tgt):
  globdefs_lsim F_lsim fprog_src fprog_tgt (PTree.unelements defs_src) (PTree.unelements defs_tgt).
Proof.
  unfold globdefs_lsim, globdef_list_lsim in *. intro i.
  rewrite ? PTree.guespec. apply list_forall2_rev in Hsim.
  revert Hsim i. generalize (rev defs_src) (rev defs_tgt).
  induction l; intros l0 Hsim i; inv Hsim; simpl; auto.
  destruct a, b1, H1. simpl in *. subst.
  destruct (peq i p0); simpl; subst; auto.
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
    end.

Lemma link_globdefs_lsim
      (F_lsim:F_lsimT)
      (main:positive)
      (defs1_src defs2_src:list (positive * globdef fundefT_src V_src))
      (defs1_tgt defs2_tgt:list (positive * globdef fundefT_tgt V_tgt))
      defs_src (Hdefs_src: link_globdefs fundef_src_dec V_src_dec (PTree.unelements defs1_src) (PTree.unelements defs2_src) = Some defs_src)
      (H1: globdefs_lsim
             F_lsim
             (mkprogram defs1_src main)
             (mkprogram defs1_tgt main)
             (PTree.unelements defs1_src)
             (PTree.unelements defs1_tgt))
      (H2: globdefs_lsim
             F_lsim
             (mkprogram defs2_src main)
             (mkprogram defs2_tgt main)
             (PTree.unelements defs2_src)
             (PTree.unelements defs2_tgt)):
  exists defs_tgt,
    link_globdefs fundef_tgt_dec V_tgt_dec (PTree.unelements defs1_tgt) (PTree.unelements defs2_tgt) = Some defs_tgt /\
    globdefs_lsim
      F_lsim
      (mkprogram (PTree.elements defs_src) main)
      (mkprogram (PTree.elements defs_tgt) main)
      defs_src defs_tgt.
Proof.
  generalize (link_globdefs_linkeq_l _ _ _ _ Hdefs_src). intro Hle1_src.
  generalize (link_globdefs_linkeq_r _ _ _ _ Hdefs_src). intro Hle2_src.
  destruct (link_globdefs fundef_tgt_dec V_tgt_dec (PTree.unelements defs1_tgt) (PTree.unelements defs2_tgt)) as [defs_tgt|] eqn:Hdefs_tgt.
  { generalize (link_globdefs_linkeq_l _ _ _ _ Hdefs_tgt). intro Hle1_tgt.
    generalize (link_globdefs_linkeq_r _ _ _ _ Hdefs_tgt). intro Hle2_tgt.
    eexists. split; [eauto|].
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
    { destruct Hdefs_src as [[]|[]], Hdefs_tgt as [[]|[]]; subst;
      repeat
        match goal with
          | [H: globfun_lsim _ _ _ _ _ |- _] => inv H
          | [H1: fundef_src_dec ?f = _, H2: fundef_src_dec ?f = _ |- _] =>
            rewrite H1 in H2; inv H2
          | [H1: fundef_tgt_dec ?f = _, H2: fundef_tgt_dec ?f = _ |- _] =>
            rewrite H1 in H2; inv H2
        end.
      - eapply globdef_lsim_le; eauto.
        + split; auto. unfold globdef_list_linkeq. rewrite Hle2_src.
          repeat intro. exists def1. split; [|reflexivity].
          simpl. rewrite PTree.unelements_elements. auto.
        + split; auto. unfold globdef_list_linkeq. rewrite Hle2_tgt.
          repeat intro. exists def1. split; [|reflexivity].
          simpl. rewrite PTree.unelements_elements. auto.
      - inv H; inv H1; inv H2; inv H3; inv Hv; inv Hv0; repeat constructor;
        repeat
          match goal with
            | [H: globfun_lsim _ _ _ _ _ |- _] => inv H
            | [H1: fundef_src_dec ?f = _, H2: fundef_src_dec ?f = _ |- _] =>
              rewrite H1 in H2; inv H2
            | [H1: fundef_tgt_dec ?f = _, H2: fundef_tgt_dec ?f = _ |- _] =>
              rewrite H1 in H2; inv H2
          end.
        + eapply globfun_lsim_e; eauto.
        + inv Hv1. destruct v1, v2; simpl in *; subst.
          unfold transf_globvar in *. simpl in *.
          destruct (transf_V gvar_info0); simpl in *; inv Hv; inv Hv0.
          inv Hv2. simpl in *. subst. auto.
      - inv H; inv H1; inv H2; inv H3; inv Hv; inv Hv0; repeat constructor;
        repeat
          match goal with
            | [H: globfun_lsim _ _ _ _ _ |- _] => inv H
            | [H1: fundef_src_dec ?f = _, H2: fundef_src_dec ?f = _ |- _] =>
              rewrite H1 in H2; inv H2
            | [H1: fundef_tgt_dec ?f = _, H2: fundef_tgt_dec ?f = _ |- _] =>
              rewrite H1 in H2; inv H2
          end.
        + eapply globfun_lsim_e; eauto.
        + inv Hv1. destruct v1, v2; simpl in *; subst.
          unfold transf_globvar in *. simpl in *.
          destruct (transf_V gvar_info0); simpl in *; inv Hv; inv Hv0.
          inv Hv2. simpl in *. subst. auto.
      - inv H; inv H1; inv H2; inv H3; inv Hv; inv Hv0; repeat constructor;
        repeat
          match goal with
            | [H: globfun_lsim _ _ _ _ _ |- _] => inv H
            | [H1: fundef_src_dec ?f = _, H2: fundef_src_dec ?f = _ |- _] =>
              rewrite H1 in H2; inv H2
            | [H1: fundef_tgt_dec ?f = _, H2: fundef_tgt_dec ?f = _ |- _] =>
              rewrite H1 in H2; inv H2
          end.
        + eapply globfun_lsim_i; eauto. intros. apply Hsim.
          * destruct Hfprog_src as [Hfdefs_src ?]. simpl in *. subst.
            split; auto. unfold globdef_list_linkeq in *.
            rewrite Hle1_src, <- Hfdefs_src.
            repeat intro. exists def1. split; [|reflexivity].
            rewrite PTree.unelements_elements. auto.
          * destruct Hfprog_tgt as [Hfdefs_tgt ?]. simpl in *. subst.
            split; auto. unfold globdef_list_linkeq in *.
            rewrite Hle1_tgt, <- Hfdefs_tgt.
            repeat intro. exists def1. split; [|reflexivity].
            rewrite PTree.unelements_elements. auto.
        + eapply globfun_lsim_e; eauto.
        + inv Hv1. destruct v1, v2; simpl in *; subst.
          unfold transf_globvar in *. simpl in *.
          destruct (transf_V gvar_info0); simpl in *; inv Hv; inv Hv0.
          inv Hv2. simpl in *. subst. auto.
    }
    { eapply globdef_lsim_le; eauto.
      - split; auto. unfold globdef_list_linkeq. rewrite Hle1_src.
        repeat intro. exists def1. split; [|reflexivity].
        simpl. rewrite PTree.unelements_elements. auto.
      - split; auto. unfold globdef_list_linkeq. rewrite Hle1_tgt.
        repeat intro. exists def1. split; [|reflexivity].
        simpl. rewrite PTree.unelements_elements. auto.
    }
    { eapply globdef_lsim_le; eauto.
      - split; auto. unfold globdef_list_linkeq. rewrite Hle2_src.
        repeat intro. exists def1. split; [|reflexivity].
        simpl. rewrite PTree.unelements_elements. auto.
      - split; auto. unfold globdef_list_linkeq. rewrite Hle2_tgt.
        repeat intro. exists def1. split; [|reflexivity].
        simpl. rewrite PTree.unelements_elements. auto.
    }
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

Lemma link_globdef_list_lsim
      (F_lsim:F_lsimT)
      (main:positive)
      (defs1_src defs2_src:list (positive * globdef fundefT_src V_src))
      (defs1_tgt defs2_tgt:list (positive * globdef fundefT_tgt V_tgt))
      defs_src (Hdefs_src: link_globdef_list fundef_src_dec V_src_dec defs1_src defs2_src = Some defs_src)
      (H1: globdef_list_lsim
             F_lsim
             (mkprogram defs1_src main)
             (mkprogram defs1_tgt main)
             defs1_src defs1_tgt)
      (H2: globdef_list_lsim
             F_lsim
             (mkprogram defs2_src main)
             (mkprogram defs2_tgt main)
             defs2_src defs2_tgt):
  exists defs_tgt,
    link_globdef_list fundef_tgt_dec V_tgt_dec defs1_tgt defs2_tgt = Some defs_tgt /\
    globdef_list_lsim
      F_lsim
      (mkprogram defs_src main)
      (mkprogram defs_tgt main)
      defs_src defs_tgt.
Proof.
  apply globdef_list_lsim_globdefs_lsim in H1.
  apply globdef_list_lsim_globdefs_lsim in H2.
  unfold link_globdef_list in Hdefs_src.
  match goal with
    | [H: context[link_globdefs ?fundef_dec ?V_dec ?defs1 ?defs2] |- _] =>
      destruct (link_globdefs fundef_dec V_dec defs1 defs2) as [defs|] eqn:Hdefs; inv H
  end.
  exploit link_globdefs_lsim; eauto. intros [defs_tgt [Hdefs_tgt Hsim]].
  unfold link_globdef_list. rewrite Hdefs_tgt. eexists. split; eauto.
  apply globdefs_lsim_globdef_list_lsim. auto.
Qed.

Section DEF.

Variable (F_lsim:F_lsimT).

Definition F_future_lsim :=
  fun fprog_src fprog_tgt f_src f_tgt =>
    forall (Hfprog: program_weak_lsim fprog_src fprog_tgt),
    F_lsim fprog_src fprog_tgt f_src f_tgt.

Definition program_lsim
           (prog_src: program fundefT_src V_src)
           (prog_tgt: program fundefT_tgt V_tgt): Prop :=
  globdef_list_lsim F_future_lsim prog_src prog_tgt prog_src.(prog_defs) prog_tgt.(prog_defs) /\
  prog_src.(prog_main) = prog_tgt.(prog_main).

Lemma link_program_lsim
      (p1_src p2_src:program fundefT_src V_src)
      (p1_tgt p2_tgt:program fundefT_tgt V_tgt)
      p_src (Hp_src: link_program fundef_src_dec V_src_dec p1_src p2_src = Some p_src)
      (H1: program_lsim p1_src p1_tgt)
      (H2: program_lsim p2_src p2_tgt):
  exists p_tgt,
    link_program fundef_tgt_dec V_tgt_dec p1_tgt p2_tgt = Some p_tgt /\
    program_lsim p_src p_tgt.
Proof.
  destruct p1_src as [defs1_src main1_src].
  destruct p1_tgt as [defs1_tgt main1_tgt].
  destruct p2_src as [defs2_src main2_src].
  destruct p2_tgt as [defs2_tgt main2_tgt].
  destruct H1 as [H1d H1m], H2 as [H2d H2m].
  unfold link_program in *. simpl in *. subst.
  destruct ((main1_tgt =? main2_tgt)%positive) eqn:Hmain; [|inv Hp_src].
  apply Pos.eqb_eq in Hmain. subst.
  destruct (link_globdef_list fundef_src_dec V_src_dec defs1_src defs2_src) as [def_list_src|] eqn:Hdef_list_src; inv Hp_src.
  exploit link_globdef_list_lsim; eauto. intros [defs_tgt [Hdefs_tgt Hsim]].
  exists (mkprogram defs_tgt main2_tgt). rewrite Hdefs_tgt. split; auto.
  constructor; auto.
Qed.

End DEF.

Lemma program_lsim_le
      (F_lsim1 F_lsim2:F_lsimT) (HF_lsim: F_lsim1 <4= F_lsim2):
  (program_lsim F_lsim1) <2= (program_lsim F_lsim2).
Proof.
  intros. destruct PR as [Hdefs Hmain]. split; auto.
  eapply globdef_list_lsim_le; eauto.
  - reflexivity.
  - reflexivity.
  - eapply list_forall2_imply; eauto. intros. simpl in *.
    destruct v1, v2, H1. simpl in *. subst.
    split; auto.
    eapply globdef_lsim_le; try reflexivity; [|eauto].
    intros. repeat intro. specialize (PR Hfprog). auto.
Qed.

Inductive fundef_sig_lsim (f_src:fundefT_src) (f_tgt:fundefT_tgt): Prop :=
| fundef_sig_lsim_intro
    (Hsig: fundef_sig_src f_src = fundef_sig_tgt f_tgt)
.

Inductive fundef_weak_lsim
          (ge_src:Genv.t fundefT_src V_src) (ge_tgt:Genv.t fundefT_tgt V_tgt)
          (f_src:fundefT_src) (f_tgt:fundefT_tgt): Prop :=
| fundef_weak_lsim_intro
    (Hsig: fundef_sig_lsim f_src f_tgt)
    b
    (Hsrc: Maps.PTree.get b ge_src.(Genv.genv_funs) = Some f_src)
    (Htgt: Maps.PTree.get b ge_tgt.(Genv.genv_funs) = Some f_tgt)
.

Section INITIALIZE.

Variable (fprog_src: program fundefT_src V_src).
Variable (fprog_tgt: program fundefT_tgt V_tgt).
Variable (F_lsim:F_lsimT).
Variable (Hfprog: program_lsim_aux F_lsim fprog_src fprog_tgt).

Inductive match_fundef (f_src:fundefT_src) (f_tgt:fundefT_tgt): Prop :=
| match_fundef_intro
    (Hsig: fundef_sig_lsim f_src f_tgt)
    (Hsim: globfun_lsim F_lsim fprog_src fprog_tgt f_src f_tgt)
.

Let ge_src := Genv.globalenv fprog_src.
Let ge_tgt := Genv.globalenv fprog_tgt.

Lemma program_lsim_match_program:
  match_program match_fundef V_lsim nil fprog_src.(prog_main) fprog_src fprog_tgt.
Proof.
  unfold match_program. destruct Hfprog as [Hfdefs Hmain].
  split; eauto. exists fprog_tgt.(prog_defs). split; [|rewrite app_nil_r; auto].
  revert Hfdefs. generalize (prog_defs fprog_src) as l1, (prog_defs fprog_tgt) as l2.
  induction l1; intros l2 Hsim; inv Hsim; constructor; auto.
  destruct a, b1, H1. simpl in *. subst.
  inv H0.
  - repeat constructor; auto.
    inv Hf; unfold fundef_sig_src, fundef_sig_tgt; rewrite Hsrc, Htgt; auto.
    exploit (Hsim fprog_src fprog_tgt); eauto; try reflexivity.
    intros [_ ?]. auto.
  - destruct v_src, v_tgt. inv Hv. unfold transf_globvar in Hv0. simpl in *.
    destruct (transf_V gvar_info) eqn:Hgvar_info; inv Hv0. constructor; auto.
Qed.
Local Hint Resolve program_lsim_match_program.

Lemma globalenvs_match:
  Genv.match_genvs match_fundef V_lsim nil (Genv.globalenv fprog_src) (Genv.globalenv fprog_tgt).
Proof. eapply Genv.globalenvs_match; eauto. Qed.
Local Hint Resolve globalenvs_match.

Lemma program_lsim_init_mem_match:
  forall m,
    Genv.init_mem fprog_src = Some m ->
    Genv.init_mem fprog_tgt = Some m.
Proof.
  intros. erewrite Genv.init_mem_match; eauto; auto.
Qed.

Lemma symbols_preserved:
  forall (s : ident),
  Genv.find_symbol (Genv.globalenv fprog_tgt) s = Genv.find_symbol (Genv.globalenv fprog_src) s.
Proof.
  intros. eapply Genv.find_symbol_match; eauto.
Qed.

Lemma varinfo_preserved:
  forall b,
    match Genv.find_var_info (Genv.globalenv fprog_tgt) b, Genv.find_var_info (Genv.globalenv fprog_src) b with
      | None, None => True
      | Some v_tgt, Some v_src =>
        transf_globvar transf_V v_src = OK v_tgt
      | _, _ => False
    end.
Proof.
  intros. case_eq (Genv.find_var_info (Genv.globalenv fprog_src) b); intros.
  - exploit Genv.find_var_info_match; eauto. intros [tv [Htv Hsim]].
    rewrite Htv. inv Hsim. inv H0.
    unfold transf_globvar, bind. simpl in *. rewrite H2. auto.
  - case_eq (Genv.find_var_info (Genv.globalenv fprog_tgt) b); intros; auto.
    exploit Genv.find_var_info_rev_match; eauto.
    destruct (plt b (Genv.genv_next (Genv.globalenv fprog_src))); [|intro X; inv X].
    intros [v [Hv Hsim]]. rewrite H in Hv. inv Hv.
Qed.

Lemma funct_ptr_translated:
  forall (b : block) (f : fundefT_src),
  Genv.find_funct_ptr (Genv.globalenv fprog_src) b = Some f ->
  exists tf : fundefT_tgt,
  Genv.find_funct_ptr (Genv.globalenv fprog_tgt) b = Some tf /\ fundef_weak_lsim ge_src ge_tgt f tf.
Proof.
  intros. exploit Genv.find_funct_ptr_match; eauto. intros [tf [Htf Hsim]].
  eexists. split; eauto. inv Hsim. inv Hsig. unfold Genv.find_funct_ptr in *.
  repeat econstructor; eauto.
Qed.

Lemma funct_ptr_translated':
  forall (b : block) (f : fundefT_src),
  Genv.find_funct_ptr (Genv.globalenv fprog_src) b = Some f ->
  exists tf : fundefT_tgt,
  Genv.find_funct_ptr (Genv.globalenv fprog_tgt) b = Some tf /\ globfun_lsim F_lsim fprog_src fprog_tgt f tf.
Proof.
  intros. exploit Genv.find_funct_ptr_match; eauto. intros [tf [Htf Hsim]].
  exists tf. split; auto. inv Hsim. auto.
Qed.

Lemma functions_translated:
  forall v f,
  Genv.find_funct (Genv.globalenv fprog_src) v = Some f ->
  exists tf, Genv.find_funct (Genv.globalenv fprog_tgt) v = Some tf /\ fundef_weak_lsim ge_src ge_tgt f tf.
Proof.
  intros. destruct v; inv H. 
  destruct (Int.eq_dec i Int.zero); inv H1.
  apply funct_ptr_translated. auto.
Qed.

Lemma sig_preserved:
  forall f tf (Hsim: fundef_sig_lsim f tf),
    fundef_sig_src f = fundef_sig_tgt tf.
Proof.
  intros. inv Hsim. auto.
Qed.

End INITIALIZE.

End PROGRAM_LSIM.
