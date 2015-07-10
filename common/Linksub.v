Require Import RelationClasses.
Require String.
Require Import Coqlib CoqlibExtra.
Require Import Maps MapsExtra.
Require Import Integers Floats Values AST Globalenvs.
Require Import Language Linker LinkerProp.

Set Implicit Arguments.


(* Future programs of a partial program after linkings *)
Section Linksub.

Variable (lang:Language).
  
Let sigT := lang.(sigT).
Let fT := lang.(fT).
Let efT := lang.(efT).
Let fundefT := lang.(fundefT).
Let vT := lang.(vT).

Let f_sig := fT.(F_sig).
Let ef_sig := efT.(EF_sig).
Let ef_dec := efT.(EF_dec).
Let fundef_dec := fundefT.(Fundef_equiv).(AtoB).
Let v_dec := vT.(V_dec).

Ltac clarify :=
  repeat
    (try match goal with
           | [H1: ?x = _, H2: ?x = _ |- _] =>
             rewrite H1 in H2; inv H2
         end;
     auto).

(** `linksub a b` means `b` is a possible future global definition of `a` after linkings *)

Definition globfun_linksub (f1 f2:fundefT): Prop :=
  f1 = f2 \/ globfun_linkable lang f1 f2.


Definition globvar_linksub (v1 v2:globvar vT): Prop :=
  v1 = v2 \/ globvar_linkable lang v1 v2.

Inductive globdef_linksub: forall (g1 g2:globdef fundefT vT), Prop :=
| globdef_linksub_fun
    f1 f2 (Hv: globfun_linksub f1 f2):
    globdef_linksub (Gfun f1) (Gfun f2)
| globdef_linksub_var
    v1 v2 (Hv: globvar_linksub v1 v2):
    globdef_linksub (Gvar v1) (Gvar v2)
.

Definition globdefs_linksub (defs1 defs2:PTree.t (globdef fundefT vT)): Prop :=
  forall var def1 (Hsrc: PTree.get var defs1 = Some def1),
  exists def2,
    PTree.get var defs2 = Some def2 /\
    globdef_linksub def1 def2.

Definition globdef_list_linksub (defs1 defs2:list (positive * globdef fundefT vT)): Prop :=
  globdefs_linksub (PTree_unelements defs1) (PTree_unelements defs2).

Definition program_linksub (p1 p2:program fundefT vT): Prop :=
  globdef_list_linksub p1.(prog_defs) p2.(prog_defs) /\
  p1.(prog_main) = p2.(prog_main).


(** preorders *)

Global Program Instance globfun_linksub_PreOrder: PreOrder globfun_linksub.
Next Obligation.
  intro f. left. auto.
Qed.
Next Obligation.
  intros f1 f2 f3 H12 H23.
  destruct H12, H23; subst; auto.
  { left. auto. }
  { right. auto. }
  { right. auto. }
  inv H; inv H0; rewrite H2 in H3; inv H3.
  - right. eapply globfun_linkable_ei; eauto.
  - right. eapply globfun_linkable_ee; eauto.
Qed.

Global Program Instance globvar_linksub_PreOrder: PreOrder globvar_linksub.
Next Obligation.
  intros [info init readonly volatile].
  constructor; auto.
Qed.
Next Obligation.
  intros v1 v2 v3 H12 H23.
  destruct H12, H23; subst; auto.
  { left. auto. }
  { right. auto. }
  { right. auto. }
  right. inv H. inv H0.
  constructor; simpl.
  - rewrite Hinfo. auto.
  - destruct Hinit; subst; auto.
  - rewrite Hreadonly. auto.
  - rewrite Hvolatile. auto.
Qed.

Global Program Instance globdef_linksub_PreOrder: PreOrder globdef_linksub.
Next Obligation.
  intros [f|v]; constructor; reflexivity.
Qed.
Next Obligation.
  intros [f1|v1] [f2|v2] [f3|v3] H12 H23; inv H12; inv H23.
  - constructor. rewrite Hv. auto.
  - constructor. rewrite Hv. auto.
Qed.

Global Program Instance globdefs_linksub_PreOrder: PreOrder globdefs_linksub.
Next Obligation.
  repeat intro. eexists. split; eauto. reflexivity.
Qed.
Next Obligation.
  repeat intro.
  exploit H; eauto. intros [ydef [Hydef Hxy]].
  exploit H0; eauto. intros [zdef [Hzdef Hyz]].
  eexists. split; eauto. rewrite Hxy. auto.
Qed.

Global Program Instance globdef_list_linksub_PreOrder: PreOrder globdef_list_linksub.
Next Obligation.
  repeat intro. eexists. split; eauto. reflexivity.
Qed.
Next Obligation.
  intros x y z Hxy Hyz. unfold globdef_list_linksub in *.
  rewrite Hxy. auto.
Qed.

Global Program Instance program_linksub_PreOrder: PreOrder program_linksub.
Next Obligation.
  repeat intro. split; reflexivity.
Qed.
Next Obligation.
  intros x y z [Hxy_defs Hxy_main] [Hyz_defs Hyz_main].
  split.
  - rewrite Hxy_defs. auto.
  - rewrite Hxy_main. auto.
Qed.


(** `linkable` and `linksub` properties *)

Lemma globdef_linkable_linksub
      g1 g2 (Hlinkable: globdef_linkable lang g1 g2):
  globdef_linksub g1 g2.
Proof.
  inv Hlinkable; constructor; auto.
  - right. auto.
  - right. auto.
Qed.


(** properties of linking on linksub *)

Lemma link_globdefs_linksub_l
      defs1 defs2 defs
      (Hdefs: link_globdefs lang defs1 defs2 = Some defs):
  globdefs_linksub defs1 defs.
Proof.
  repeat intro.
  exploit gtlink_globdefs; eauto. instantiate (1 := var).
  unfold fundefT, vT in *. rewrite Hsrc.
  destruct (defs2 ! var) as [def2|], (defs ! var) as [def|]; intro X; inv X.
  - destruct H. subst. eexists. split; eauto.
    apply globdef_linkable_linksub. auto.
  - destruct H. subst. eexists. split; eauto.
    reflexivity.
  - eexists. split; eauto.
    reflexivity.
Qed.

Lemma link_globdefs_linksub_r
      defs1 defs2 defs
      (Hdefs: link_globdefs lang defs1 defs2 = Some defs):
  globdefs_linksub defs2 defs.
Proof.
  repeat intro.
  exploit gtlink_globdefs; eauto. instantiate (1 := var).
  unfold fundefT, vT in *. rewrite Hsrc.
  destruct (defs1 ! var) as [d1|], (defs ! var) as [d|]; intro X; inv X.
  - destruct H. subst. eexists. split; eauto.
    reflexivity.
  - destruct H. subst. eexists. split; eauto.
    apply globdef_linkable_linksub. auto.
  - eexists. split; eauto.
    reflexivity.
Qed.

Lemma link_globdef_list_linksub_l
      defs1 defs2 defs
      (Hdefs: link_globdef_list lang defs1 defs2 = Some defs):
  globdef_list_linksub defs1 defs.
Proof.
  unfold globdef_list_linksub, link_globdef_list in *.
  match goal with
    | [H: context[link_globdefs ?lang ?defs1 ?defs2] |- _] =>
      destruct (link_globdefs lang defs1 defs2) as [defs'|] eqn:Hdefs'; inv H
  end.
  repeat intro. exploit link_globdefs_linksub_l; eauto.
  intros [def2 [Hdef2 Hlinksub]]. exists def2. split; auto.
  rewrite PTree_unelements_elements. auto.
Qed.

Lemma link_globdef_list_linksub_r
      defs1 defs2 defs
      (Hdefs: link_globdef_list lang defs1 defs2 = Some defs):
  globdef_list_linksub defs2 defs.
Proof.
  unfold globdef_list_linksub, link_globdef_list in *.
  match goal with
    | [H: context[link_globdefs lang ?defs1 ?defs2] |- _] =>
      destruct (link_globdefs lang defs1 defs2) as [defs'|] eqn:Hdefs'; inv H
  end.
  repeat intro. exploit link_globdefs_linksub_r; eauto.
  intros [def2 [Hdef2 Hlinksub]]. exists def2. split; auto.
  rewrite PTree_unelements_elements. auto.
Qed.

Lemma link_program_linksub_l
      p1 p2 p (Hp: link_program lang p1 p2 = Some p):
  program_linksub p1 p.
Proof.
  destruct p1 as [defs1 main1].
  destruct p2 as [defs2 main2].
  destruct p as [defs main].
  unfold link_program in Hp. simpl in *.
  destruct ((main1 =? main2)%positive) eqn:Hmain; inv Hp.
  apply Pos.eqb_eq in Hmain. subst.
  match goal with
    | [H: context[link_globdef_list lang ?defs1 ?defs2] |- _] =>
      destruct (link_globdef_list lang defs1 defs2) as [defs'|] eqn:Hdefs'; inv H
  end.
  split; simpl; auto.
  eapply link_globdef_list_linksub_l. eauto.
Qed.

Lemma link_program_linksub_r
      p1 p2 p (Hp: link_program lang p1 p2 = Some p):
  program_linksub p2 p.
Proof.
  destruct p1 as [defs1 main1].
  destruct p2 as [defs2 main2].
  destruct p as [defs main].
  unfold link_program in Hp. simpl in *.
  destruct ((main1 =? main2)%positive) eqn:Hmain; inv Hp.
  apply Pos.eqb_eq in Hmain. subst.
  match goal with
    | [H: context[link_globdef_list lang ?defs1 ?defs2] |- _] =>
      destruct (link_globdef_list lang defs1 defs2) as [defs'|] eqn:Hdefs'; inv H
  end.
  split; simpl; auto.
  eapply link_globdef_list_linksub_r. eauto.
Qed.

End Linksub.

Lemma find_symbol_spec F V (p:program F V) i:
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
  Ltac clarify_find_symbol_spec :=
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
  induction (rev defs); simpl; [rewrite PTree.gempty; auto|].
  rewrite ? PTree.gsspec. destruct a. simpl.
  destruct (peq i i0); [subst|]; simpl; [destruct g| ]; clarify_find_symbol_spec;
  try (match goal with [H: (Genv.genv_vars _)!_=_ |- _] =>
                       apply Genv.genv_vars_range in H; xomega end);
  try (match goal with [H: (Genv.genv_funs _)!_=_ |- _] =>
                       apply Genv.genv_funs_range in H; xomega end).
Qed.

Definition defines_internal lang (ge:Genv.t _ lang.(vT)) id f :=
  exists b,
    Genv.find_symbol ge id = Some b /\
    Genv.find_funct_ptr ge b = Some (BtoA lang.(fundefT) (inl f)).

Lemma program_linksub_internal lang sprog prog id f
      (Hlink: program_linksub lang sprog prog)
      (Hf: defines_internal lang (Genv.globalenv sprog) id f):
  defines_internal lang (Genv.globalenv prog) id f.
Proof.
  Ltac finishF :=try (intro FALSO; inv FALSO).
  destruct Hf as [b [G F]].
  generalize (find_symbol_spec sprog id). rewrite G, F, <- PTree_guespec.
  destruct ((PTree_unelements _) ! _) as [[]|] eqn:Hg; finishF.
  destruct (Genv.find_var_info (Genv.globalenv sprog) b); finishF.
  apply Hlink in Hg. destruct Hg as [g' [G' LINK]]. inv LINK. inv Hv;
    [|inv H; rewrite HBAB in *; inv H1].
  generalize (find_symbol_spec prog id). rewrite <- PTree_guespec, G'.
  destruct (Genv.find_symbol (Genv.globalenv prog) id) eqn:Hg'; finishF.
  destruct (Genv.find_funct_ptr (Genv.globalenv prog) b0) eqn:Hf'; finishF.
  destruct (Genv.find_var_info (Genv.globalenv prog) b0) eqn:Hv'; finishF.
  eexists. split; eauto.
Qed.
