Require Import RelationClasses.
Require String.
Require Import Coqlib Coqlib_linker.
Require Import Maps_linker.
Require Import Integers Floats Values AST Globalenvs.
Require Import LinkerSpecification.

Set Implicit Arguments.


(* properties of linker *)
Section LINKER_PROP.

Variable (F V:Type).  
Variable (V_dec: forall (v1 v2:V), {v1 = v2} + {v1 <> v2}).

Lemma gflink_globdefs defs1 defs2 (Hlink: @link_globdefs F V V_dec defs1 defs2 = None):
  exists var def1 def2,
    PTree.get var defs1 = Some def1 /\
    PTree.get var defs2 = Some def2 /\
    ~ globdef_linkable def1 def2 /\
    ~ globdef_linkable def2 def1.
Proof.
  unfold link_globdefs in Hlink.
  match goal with
    | [H: context[PTree_Properties.for_all ?m ?f] |- _] =>
      destruct (PTree_Properties.for_all m f) eqn:Hlinkable; inv Hlink
  end.
  apply PTree_Properties.for_all_false in Hlinkable.
  destruct Hlinkable as [i [x [Hx1 Hx2]]].
  destruct x; inv Hx2. rewrite PTree.gcombine in Hx1; auto.
  destruct (defs1 ! i) eqn:Hi1, (defs2 ! i) eqn:Hi2; inv Hx1.
  destruct (globdef_linkable_dec V_dec g g0); inv H0.
  destruct (globdef_linkable_dec V_dec g0 g); inv H1.
  repeat eexists; eauto.
Qed.

Lemma gtlink_globdefs defs1 defs2 defs (Hlink: @link_globdefs F V V_dec defs1 defs2 = Some defs):
  forall var,
    match PTree.get var defs1, PTree.get var defs2, PTree.get var defs with
      | Some g1, Some g2, Some g =>
        (globdef_linkable g1 g2 /\ g2 = g) \/
        (globdef_linkable g2 g1 /\ g1 = g)
      | Some g1, None, Some g => g1 = g
      | None, Some g2, Some g => g2 = g
      | None, None, None => True
      | _, _, _ => False
    end.
Proof.
  intro i. unfold link_globdefs in Hlink.
  match goal with
    | [H: context[PTree_Properties.for_all ?m ?f] |- _] =>
      destruct (PTree_Properties.for_all m f) eqn:Hlinkable; inv Hlink
  end.
  rewrite PTree.goption_map, PTree.gcombine; auto.
  destruct (defs1 ! i) eqn:Hi1, (defs2 ! i) eqn:Hi2; auto.
  destruct (globdef_linkable_dec V_dec g g0).
  { left. split; auto. }
  destruct (globdef_linkable_dec V_dec g0 g).
  { right. split; auto. }
  eapply PTree_Properties.for_all_correct in Hlinkable; eauto.
  { instantiate (1 := None) in Hlinkable. inv Hlinkable. }
  instantiate (1 := i). rewrite PTree.gcombine; auto.
  rewrite Hi1, Hi2.
  destruct (globdef_linkable_dec V_dec g g0); try (contradict n; auto; fail).
  destruct (globdef_linkable_dec V_dec g0 g); try (contradict n0; auto; fail).
  auto.
Qed.

End LINKER_PROP.


(* lifting function simulation to program simulation *)
Section PROGRAM_SIM.

Variable (F_src F_tgt V:Type).
Variable (V_dec: forall (v1 v2:V), {v1 = v2} + {v1 <> v2}).

Parameter F_sim: forall (f_src:F_src) (f_tgt:F_tgt), Prop.

Inductive globfun_sim: forall (g_src:AST.fundef F_src) (g_tgt:AST.fundef F_tgt), Prop :=
| globfun_sim_i
    f_src f_tgt
    (Hf: F_sim f_src f_tgt):
    globfun_sim (Internal f_src) (Internal f_tgt)
| globfun_sim_e e:
    globfun_sim (External e) (External e)
.

Inductive globdef_sim: forall (g_src:globdef (AST.fundef F_src) V) (g_tgt:globdef (AST.fundef F_tgt) V), Prop :=
| globdef_sim_fun
    f_src f_tgt (Hf: globfun_sim f_src f_tgt):
    globdef_sim (Gfun f_src) (Gfun f_tgt)
| globdef_sim_var v:
    globdef_sim (Gvar v) (Gvar v)
.

Definition globdefs_sim
           (defs_src:PTree.t (globdef (AST.fundef F_src) V))
           (defs_tgt:PTree.t (globdef (AST.fundef F_tgt) V)):
  Prop :=
  forall i,
    match PTree.get i defs_src, PTree.get i defs_tgt with
      | Some g1, Some g2 => globdef_sim g1 g2
      | None, None => True
      | _, _ => False
    end.

Definition globdef_list_sim
           (defs_src:list (positive * globdef (AST.fundef F_src) V))
           (defs_tgt:list (positive * globdef (AST.fundef F_tgt) V)):
  Prop :=
  list_forall2
    (fun g_src g_tgt =>
       fst g_src = fst g_tgt /\
       globdef_sim (snd g_src) (snd g_tgt))
    defs_src defs_tgt.

Definition program_sim
           (p_src:program (AST.fundef F_src) V) (p_tgt:program (AST.fundef F_tgt) V): Prop :=
  globdef_list_sim p_src.(prog_defs) p_tgt.(prog_defs) /\
  p_src.(prog_main) = p_tgt.(prog_main).

Lemma globdefs_sim_globdef_list_sim
      (defs_src: PTree.t (globdef (AST.fundef F_src) V))
      (defs_tgt: PTree.t (globdef (AST.fundef F_tgt) V))
      (Hsim: globdefs_sim defs_src defs_tgt):
  globdef_list_sim (PTree.elements defs_src) (PTree.elements defs_tgt).
Proof.
  apply PTree.elements_canonical_order; intros.
  - exploit Hsim. instantiate (1 := i). rewrite H. intro X.
    destruct (defs_tgt ! i) eqn:Hi_tgt; [|inv X].
    eexists. split; eauto.
  - exploit Hsim. instantiate (1 := i). rewrite H. intro X.
    destruct (defs_src ! i) eqn:Hi_src; [|inv X].
    eexists. split; eauto.
Qed.

Lemma globdef_list_sim_globdefs_sim
      (defs_src: list (positive * globdef (AST.fundef F_src) V))
      (defs_tgt: list (positive * globdef (AST.fundef F_tgt) V))
      (Hsim: globdef_list_sim defs_src defs_tgt):
  globdefs_sim (PTree.unelements defs_src) (PTree.unelements defs_tgt).
Proof.
  unfold PTree.unelements. rewrite <- ? fold_left_rev_right.
  unfold globdef_list_sim in Hsim. apply list_forall2_rev in Hsim.
  revert Hsim. generalize (rev defs_src) (rev defs_tgt). clear defs_src defs_tgt.
  induction l; intros l2 H; inv H; simpl.
  { intro. rewrite ? PTree.gempty. auto. }
  destruct H2, a, b1. simpl in *. subst.
  intro. rewrite ? PTree.gsspec. destruct (peq i p0); subst; auto.
  apply IHl. auto.
Qed.

Lemma link_globdefs_sim
      (defs1_src defs2_src:PTree.t (globdef (AST.fundef F_src) V))
      (defs1_tgt defs2_tgt:PTree.t (globdef (AST.fundef F_tgt) V))
      defs_src (Hdefs_src: link_globdefs V_dec defs1_src defs2_src = Some defs_src)
      (H1: globdefs_sim defs1_src defs1_tgt)
      (H2: globdefs_sim defs2_src defs2_tgt):
  exists defs_tgt,
    link_globdefs V_dec defs1_tgt defs2_tgt = Some defs_tgt /\
    globdefs_sim defs_src defs_tgt.
Proof.
  destruct (link_globdefs V_dec defs1_tgt defs2_tgt) eqn:Hdefs_tgt.
  { eexists. split; [eauto|].
    intro i. rename t into defs_tgt.
    eapply gtlink_globdefs in Hdefs_src. instantiate (1 := i) in Hdefs_src.
    eapply gtlink_globdefs in Hdefs_tgt. instantiate (1 := i) in Hdefs_tgt.
    specialize (H1 i). specialize (H2 i).
    destruct (defs1_src ! i) eqn:Hi1_src, (defs2_src ! i) eqn:Hi2_src, (defs_src ! i) eqn:Hi_src; subst; try (inv Hdefs_src; fail);
    destruct (defs1_tgt ! i) eqn:Hi1_tgt, (defs2_tgt ! i) eqn:Hi2_tgt, (defs_tgt ! i) eqn:Hi_tgt; subst; try (inv Hdefs_tgt; fail);
    try (inv H1; fail); try (inv H2; fail); auto.
    destruct Hdefs_src as [[]|[]], Hdefs_tgt as [[]|[]]; subst; auto.
    { inv H; inv H1; inv H2; inv H3; inv Hv; inv Hv0; try inv Hf; try inv Hf0.
      { repeat constructor. }
      { destruct v1, v2; simpl in *.
        rewrite Hinfo, Hinit, Hinit0, Hreadonly, Hvolatile.
        constructor.
      }
    }
    { inv H; inv H1; inv H2; inv H3; inv Hv; inv Hv0; try inv Hf; try inv Hf0.
      { repeat constructor. }
      { destruct v1, v2; simpl in *.
        rewrite Hinfo, Hinit, Hinit0, Hreadonly, Hvolatile.
        constructor.
      }
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
    { inv H1; inv H2; inv H; try inv Hf; try inv Hf0.
      { inv Hv. }
      { inv Hv. }
      { contradict H12. repeat constructor. }
      { inv Hv. contradict H12. repeat constructor. }
      { contradict H12. constructor. auto. }
    }
    { inv H1; inv H2; inv H; try inv Hf; try inv Hf0.
      { inv Hv. }
      { contradict H21. repeat constructor. }
      { inv Hv. }
      { inv Hv. contradict H12. repeat constructor. }
      { contradict H21. constructor. auto. }
    }
  }
Qed.

Lemma link_globdef_list_sim
      (defs1_src defs2_src:list (positive * globdef (AST.fundef F_src) V))
      (defs1_tgt defs2_tgt:list (positive * globdef (AST.fundef F_tgt) V))
      defs_src (Hdefs_src: link_globdef_list V_dec defs1_src defs2_src = Some defs_src)
      (H1: globdef_list_sim defs1_src defs1_tgt)
      (H2: globdef_list_sim defs2_src defs2_tgt):
  exists defs_tgt,
    link_globdef_list V_dec defs1_tgt defs2_tgt = Some defs_tgt /\
    globdef_list_sim defs_src defs_tgt.
Proof.
  apply globdef_list_sim_globdefs_sim in H1.
  apply globdef_list_sim_globdefs_sim in H2.
  unfold link_globdef_list in Hdefs_src.
  match goal with
    | [H: context[link_globdefs ?V_dec ?defs1 ?defs2] |- _] =>
      destruct (link_globdefs V_dec defs1 defs2) as [defs|] eqn:Hdefs; inv H
  end.
  exploit link_globdefs_sim; eauto. intros [defs_tgt [Hdefs_tgt Hsim]].
  unfold link_globdef_list. rewrite Hdefs_tgt. eexists. split; eauto.
  apply globdefs_sim_globdef_list_sim. auto.
Qed.

Lemma link_program_sim
      (p1_src p2_src:program (AST.fundef F_src) V)
      (p1_tgt p2_tgt:program (AST.fundef F_tgt) V)
      p_src (Hm_src: link_program V_dec p1_src p2_src = Some p_src)
      (H1: program_sim p1_src p1_tgt)
      (H2: program_sim p2_src p2_tgt):
  exists m_tgt,
    link_program V_dec p1_tgt p2_tgt = Some m_tgt /\
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
  destruct (link_globdef_list V_dec defs1_src defs2_src) as [defs_src|] eqn:Hdef_src; inv Hm_src.
  exploit link_globdef_list_sim; eauto.
  intros [defs_tgt [Hdefs_tgt Hsim]].
  rewrite Hdefs_tgt. eexists. split; eauto.
  split; auto.
Qed.


Section INITIALIZE.

Variable (p_src: program (AST.fundef F_src) V).
Variable (p_tgt: program (AST.fundef F_tgt) V).
Variable (Hp: program_sim p_src p_tgt).

Lemma program_sim_match_program:
  match_program globfun_sim eq nil p_src.(prog_main) p_src p_tgt.
Proof.
  destruct Hp as [Hdefs Hmain].
  unfold match_program. split; eauto.
  exists p_tgt.(prog_defs). split; [|rewrite app_nil_r; auto].
  eapply list_forall2_imply; eauto. intros.
  destruct H1 as [H1 H2].
  destruct v1 as [var1 g1], v2 as [var2 g2]. simpl in *. subst.
  inv H2.
  - constructor. auto.
  - destruct v. constructor. auto.
Qed.

Lemma globalenvs_match:
  Genv.match_genvs globfun_sim eq nil (Genv.globalenv p_src) (Genv.globalenv p_tgt).
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
  forall (b : block) (f : AST.fundef F_src),
  Genv.find_funct_ptr (Genv.globalenv p_src) b = Some f ->
  exists tf : AST.fundef F_tgt,
  Genv.find_funct_ptr (Genv.globalenv p_tgt) b = Some tf /\ globfun_sim f tf.
Proof.
  generalize program_sim_match_program. intros Hmatch b f Hf.
  eapply Genv.find_funct_ptr_match; eauto.
Qed.

End INITIALIZE.

End PROGRAM_SIM.
