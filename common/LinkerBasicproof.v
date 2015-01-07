Require Import RelationClasses.
Require String.
Require Import Coqlib Coqlib_linker.
Require Import Maps Maps_linker.
Require Import Integers Floats Values AST Globalenvs.
Require Import Errors Behaviors Compiler Smallstep.
Require Import Language Linker LinkerProp.

(** lemma on link_globdefs *)

Lemma link_globdefs_morphism
      lang p1 p2 p p1' p2'
      (H: link_globdefs lang p1 p2 = Some p)
      (H1: PTree_eq p1 p1') (H2: PTree_eq p2 p2'):
  exists p',
    link_globdefs lang p1' p2' = Some p' /\
    PTree_eq p p'.
Proof.
  admit.
Qed.

(** Lemma on transform_program_globdef *)

Lemma find_map_transform_program_globdef A B V (tf:A->B) (p:list (ident * globdef A V)) i:
  find
    (fun id : positive * globdef B V => peq i (fst id))
    (map (transform_program_globdef tf) p) =
  option_map
    (transform_program_globdef tf)
    (find (fun id : positive * globdef A V => peq i (fst id)) p).
Proof.
  induction p; simpl; auto.
  unfold transform_program_globdef in *. destruct a. destruct g; simpl.
  - destruct (peq i i0); subst; simpl; auto.
  - destruct (peq i i0); subst; simpl; auto.
Qed.

Lemma option_map_snd_transform_program_globdef A B V (tf:A->B) (g:option (ident * globdef A V)):
  option_map snd (option_map (transform_program_globdef tf) g) =
  match option_map snd g with
    | Some (Gfun f) => Some (Gfun (tf f))
    | Some (Gvar v) => Some (Gvar v)
    | None => None
  end.
Proof. destruct g; auto. destruct p. destruct g; auto. Qed.

Lemma PTree_unelements_map_transform_program_globdef A B V (tf:A->B) (p:list (ident * globdef A V)):
  PTree_eq
    (PTree_unelements (map (transform_program_globdef tf) p))
    (PTree.map
       (fun i g =>
          match g with
            | Gfun f => Gfun (tf f)
            | Gvar v => Gvar v
          end)
       (PTree_unelements p)).
Proof.
  unfold PTree_unelements. rewrite <- ? fold_left_rev_right.
  rewrite <- map_rev. unfold ident in *. simpl in *.
  induction (rev p); simpl.
  { constructor. intros. rewrite PTree.gmap, ? PTree.gempty. auto. }
  inv IHl. constructor. intros. specialize (H i).
  rewrite ? PTree.gmap, ? PTree.gsspec in *. destruct a. destruct g; simpl.
  - destruct (peq i p0); auto.
  - destruct (peq i p0); auto.
Qed.

Lemma map_transform_program_globdef_PTree_elements A B V (tf:A->B) (p:PTree.t (globdef A V)):
  map (transform_program_globdef tf) (PTree.elements p) =
  PTree.elements
    (PTree.map
       (fun i g =>
          match g with
            | Gfun f => Gfun (tf f)
            | Gvar v => Gvar v
          end)
       p).
Proof.
  exploit (PTree.elements_canonical_order
             (fun g1 g2 => g2 =
                           match g1 with
                             | Gfun f => Gfun (tf f)
                             | Gvar v => Gvar v
                           end)
             p
             (PTree.map
                (fun (_ : positive) (g : globdef A V) =>
                   match g with
                     | Gfun f => Gfun (tf f)
                     | Gvar v => Gvar v
                   end) p)).
  - intros. eexists. split; auto. rewrite PTree.gmap, H. auto.
  - intros. rewrite PTree.gmap in H. destruct (p ! i) eqn:Hpi; inv H. eexists. split; auto.
  - generalize ((PTree.elements
                   (PTree.map
                      (fun (_ : positive) (g : globdef A V) =>
                         match g with
                           | Gfun f => Gfun (tf f)
                           | Gvar v => Gvar v
                         end) p))).
    generalize (PTree.elements p). clear p.
    induction l; intros l0 X; inv X; auto.
    destruct a, b1, H1 as [? ?]. simpl in *. subst.
    f_equal; auto. destruct g; auto.
Qed.

(** lemma on transform_program *)

Lemma transform_program_link_program
      (fT1 fT2:F Sig_signature) vT
      (tf:fT1 -> fT2)
      (p1 p2 p:(mkLanguage (Fundef_common fT1) vT).(progT))
      (q1 q2:(mkLanguage (Fundef_common fT2) vT).(progT))
      (Hp: link_program (mkLanguage (Fundef_common fT1) vT) p1 p2 = Some p)
      (H1: transform_program (AST.transf_fundef tf) p1 = q1)
      (H2: transform_program (AST.transf_fundef tf) p2 = q2):
  exists q,
    link_program (mkLanguage (Fundef_common fT2) vT) q1 q2 = Some q /\
    transform_program (AST.transf_fundef tf) p = q.
Proof.
  Ltac clarify :=
    repeat match goal with
             | [H: context[match ?d with | Some _ => _ | None => _ end] |- _] =>
               let defs := fresh "defs" in
               let Hdefs := fresh "Hdefs" in
               destruct d as [defs|] eqn:Hdefs; inv H; simpl in *
             | [|- context[match ?d with | Some _ => _ | None => _ end]] =>
               let defs := fresh "defs" in
               let Hdefs := fresh "Hdefs" in
               destruct d as [defs|] eqn:Hdefs; simpl in *
           end.
  unfold progT in *. simpl in *. subst.
  unfold link_program, transform_program in *. simpl in *.
  destruct p1 as [p1 mainp1], p2 as [p2 mainp2]. simpl in *.
  destruct (Pos.eqb mainp1 mainp2); [|inv Hp]. clarify.
  - unfold link_globdef_list in *. clarify.
    eexists. split; eauto. repeat f_equal.
    eapply (link_globdefs_morphism (mkLanguage (Fundef_common fT2) vT)) in Hdefs1;
      try apply PTree_unelements_map_transform_program_globdef. simpl in *.
    destruct Hdefs1 as [defs1' [Hdefs1' Hdefs1]]. rewrite (PTree_elements_extensional' Hdefs1).
    clear defs1 Hdefs1.
    revert Hdefs0 Hdefs1'. generalize (PTree_unelements p1) (PTree_unelements p2).
    clear p1 p2. intros p1 p2 Hdefs0 Hdefs1'.
    rewrite map_transform_program_globdef_PTree_elements.
    apply PTree_elements_extensional'. constructor. intro. rewrite PTree.gmap.
    eapply (gtlink_globdefs (mkLanguage (Fundef_common fT1) vT)) in Hdefs0. instantiate (1 := i) in Hdefs0.
    eapply (gtlink_globdefs (mkLanguage (Fundef_common fT2) vT)) in Hdefs1'. instantiate (1 := i) in Hdefs1'.
    rewrite PTree.gmap in *. unfold ident in *. simpl in *.
    destruct (p1 ! i); simpl in *; rewrite PTree.gmap in *;
    destruct (p2 ! i), (defs0 ! i), (defs1' ! i); simpl in *; subst; auto;
    try match goal with
          | [H: False |- _] => inv H
        end.
    destruct Hdefs0 as [[? ?]|[? ?]], Hdefs1' as [[? ?]|[? ?]]; subst; auto.
    + admit.
    + admit.
  - exfalso. unfold link_globdef_list in *. clarify.
    eapply (gflink_globdefs (mkLanguage (Fundef_common fT2) vT)) in Hdefs1. simpl in *.
    destruct Hdefs1 as [i [tdef1 [tdef2 [Htdef1 [Htdef2 [Htdefs1 Htdefs2]]]]]].
    eapply (gtlink_globdefs (mkLanguage (Fundef_common fT1) vT)) in Hdefs0. instantiate (1 := i) in Hdefs0. simpl in *.
    rewrite PTree_guespec in Htdef1. rewrite PTree_guespec in Htdef2.
    rewrite <- map_rev in *. rewrite ? PTree_guespec in Hdefs0.
    rewrite find_map_transform_program_globdef in *.
    rewrite option_map_snd_transform_program_globdef in *.
    clarify.
    unfold ident in *. rewrite Hdefs, Hdefs1 in Hdefs0. clarify.
    + destruct H as [H ?]. subst.
      contradict Htdefs1. inv H.
      * inv H0. inv H1. constructor. admit.
      * inv H0. inv H1. constructor. inv Hv. constructor; auto.
    + destruct H as [H ?]. subst.
      contradict Htdefs2. inv H.
      * inv H0. inv H1. constructor. admit.
      * inv H0. inv H1. constructor. inv Hv. constructor; auto.
Qed.

Lemma transform_partial_program2_link_program
      (lang_src lang_tgt:Language)
      (tf:lang_src.(fundefT)->res lang_tgt.(fundefT))
      (tv:lang_src.(vT)->res lang_tgt.(vT))
      p1 p2 p q1 q2
      (Hp: link_program lang_src p1 p2 = Some p)
      (H1: transform_partial_program2 tf tv p1 = OK q1)
      (H2: transform_partial_program2 tf tv p2 = OK q2):
  exists q,
    link_program lang_tgt q1 q2 = Some q /\
    transform_partial_program2 tf tv p = OK q.
Proof.
  destruct p1 as [p1 mainp1], p2 as [p2 mainp2], q1 as [q1 mainq1], q2 as [q2 mainq2].
  rewrite transform_partial_program2_augment in *. simpl in *.
  apply transform_partial_augment_program_match in H1. destruct H1 as [[qdefs1 [Hqdefs1 ?]] Hmain1].
  apply transform_partial_augment_program_match in H2. destruct H2 as [[qdefs2 [Hqdefs2 ?]] Hmain2].
  simpl in *. rewrite app_nil_r in *. symmetry in H, H0. subst.
  unfold link_program in *. simpl in *. destruct (Pos.eqb mainp1 mainp2) eqn:Hmainp; [|inv Hp].
  apply Peqb_true_eq in Hmainp. subst.
  admit.
Qed.
