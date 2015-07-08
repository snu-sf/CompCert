Require Import RelationClasses.
Require String.
Require Import Coqlib CoqlibExtra.
Require Import Maps MapsExtra.
Require Import Integers Floats Values AST Globalenvs.
Require Import Errors Behaviors Smallstep.
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
  unfold link_globdefs in *.
  erewrite PTree_Properties_for_all_morphism in H;
    [|apply PTree_combine_morphism; eauto].
  match goal with
    | [H: context[if ?b then _ else _] |- _] => destruct b; inv H
  end.
  eexists. split; auto.
  apply PTree_option_map_morphism.
  apply PTree_combine_morphism; auto.
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
      (tf:fT1 -> fT2) (Htf: forall (f:fT1), fT1.(F_sig) f = fT2.(F_sig) (tf f))
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
             | [H: False |- _] => inv H
             | [H: inl _ = inl _ |- _] => inv H
             | [H: inl _ = inr _ |- _] => inv H
             | [H: inr _ = inl _ |- _] => inv H
             | [H: inr _ = inr _ |- _] => inv H
             | [Hl: ?a = inl _, Hr: ?a = inl _ |- _] => rewrite Hl in Hr; inv Hr
             | [Hl: ?a = inl _, Hr: ?a = inr _ |- _] => rewrite Hl in Hr; inv Hr
             | [Hl: ?a = inr _, Hr: ?a = inl _ |- _] => rewrite Hl in Hr; inv Hr
             | [Hl: ?a = inr _, Hr: ?a = inr _ |- _] => rewrite Hl in Hr; inv Hr

             | [H: context[match ?d with | Some _ => _ | None => _ end] |- _] =>
               let defs := fresh "defs" in
               let Hdefs := fresh "Hdefs" in
               destruct d as [defs|] eqn:Hdefs; inv H; simpl in *
             | [|- context[match ?d with | Some _ => _ | None => _ end]] =>
               let defs := fresh "defs" in
               let Hdefs := fresh "Hdefs" in
               destruct d as [defs|] eqn:Hdefs; simpl in *
           end;
    auto.
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
    destruct (p2 ! i), (defs0 ! i), (defs1' ! i); simpl in *; subst; auto; clarify.
    destruct Hdefs0 as [[? ?]|[? ?]], Hdefs1' as [[? ?]|[? ?]]; subst; auto.
    + inv H; inv H1; simpl in *.
      * destruct f1, f2; inv Hv; inv Hv0; simpl in *; clarify.
      * inv Hv. inv Hv0. destruct v1, v2. simpl in *. repeat f_equal; auto.
        rewrite Hinit, Hinit0. auto.
    + inv H; inv H1; simpl in *.
      * destruct f1, f2; inv Hv; inv Hv0; simpl in *; clarify.
      * inv Hv. inv Hv0. destruct v1, v2. simpl in *. repeat f_equal; auto.
        rewrite Hinit, Hinit0. auto.
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
      * inv H0. inv H1. constructor.
        destruct f1, f2; inv Hv; simpl in *; clarify.
        eapply globfun_linkable_ei; simpl; eauto. rewrite <- Htf. auto.
        eapply globfun_linkable_ee; simpl; eauto.
      * inv H0. inv H1. constructor. inv Hv. constructor; auto.
    + destruct H as [H ?]. subst.
      contradict Htdefs2. inv H.
      * inv H0. inv H1. constructor.
        destruct f1, f2; inv Hv; simpl in *; clarify.
        eapply globfun_linkable_ei; simpl; eauto. rewrite <- Htf. auto.
        eapply globfun_linkable_ee; simpl; eauto.
      * inv H0. inv H1. constructor. inv Hv. constructor; auto.
Qed.

(** lemma on transform_partial_program2 *)

Inductive match_globdef_aux {A B V W : Type} (match_fundef : A -> B -> Prop)
          (match_varinfo : V -> W -> Prop)
            : globdef A V -> globdef B W -> Prop :=
    match_glob_fun : forall (f1 : A) (f2 : B),
                     match_fundef f1 f2 ->
                     match_globdef_aux match_fundef match_varinfo 
                       (Gfun f1) (Gfun f2)
  | match_glob_var : forall (init : list init_data)
                       (ro vo : bool) (info1 : V) (info2 : W),
                     match_varinfo info1 info2 ->
                     match_globdef_aux match_fundef match_varinfo
                       (Gvar
                          {|
                            gvar_info := info1;
                            gvar_init := init;
                            gvar_readonly := ro;
                            gvar_volatile := vo |})
                       (Gvar
                          {|
                            gvar_info := info2;
                            gvar_init := init;
                            gvar_readonly := ro;
                            gvar_volatile := vo |})
.

Lemma list_forall2_match_globdef_PTree_unelements A B V W
      (tf:A->B->Prop) (vi:V->W->Prop) p q
      (H: list_forall2 (match_globdef tf vi) p q):
  PTree_rel
    (fun g1 g2 => match_globdef_aux tf vi g1 g2)
    (PTree_unelements p)
    (PTree_unelements q).
Proof.
  constructor. intro. rewrite ? PTree_guespec.
  apply list_forall2_rev in H. revert H.
  unfold ident in *. simpl in *. generalize (rev p) (rev q).
  induction l; intros l0 H; inv H; simpl; auto.
  destruct a. simpl. destruct (peq i p0); subst; simpl.
  - inv H2.
    + simpl. destruct (peq p0 p0); subst; simpl; [|xomega].
      constructor. auto.
    + simpl. destruct (peq p0 p0); subst; simpl; [|xomega].
      constructor. auto.
  - inv H2.
    + simpl. destruct (peq i p0); subst; simpl; [xomega|].
      apply IHl. auto.
    + simpl. destruct (peq i p0); subst; simpl; [xomega|].
      apply IHl. auto.
Qed.

Lemma PTree_rel_PTree_elements A B V W
      (tf:A->B->Prop) (vi:V->W->Prop) p q
      (H: PTree_rel
            (fun g1 g2 => match_globdef_aux tf vi g1 g2)
            p q):
  list_forall2 (match_globdef tf vi) (PTree.elements p) (PTree.elements q).
Proof.
  exploit (PTree.elements_canonical_order (match_globdef_aux tf vi) p q).
  - intros. inv H. specialize (H1 i). rewrite H0 in H1.
    destruct (q ! i); [|inv H1]. eexists. split; auto.
  - intros. inv H. specialize (H1 i). rewrite H0 in H1.
    destruct (p ! i); [|inv H1]. eexists. split; auto.
  - generalize (PTree.elements p) (PTree.elements q). clear p q H.
    induction l; intros l0 X; inv X; constructor; auto.
    destruct a, b1, H1. simpl in *. subst.
    inv H0; constructor; auto.
Qed.

Lemma list_forall2_match_globdef_find {A B V W}
      i p1 p2
      (ti:A -> B -> Prop) (tv:V -> W -> Prop)
      (Hp: list_forall2 (match_globdef ti tv) p1 p2):
  match find (fun id : positive * globdef A V => peq i (fst id)) p1,
        find (fun id : positive * globdef B W => peq i (fst id)) p2
  with
    | Some g1, Some g2 => match_globdef ti tv g1 g2
    | None, None => True
    | _, _ => False
  end.
Proof.
  revert p2 Hp. induction p1; intros p2 Hv; inv Hv; simpl; auto.
  inv H1.
  - simpl. destruct (peq i id); subst; simpl.
    + constructor. auto.
    + apply IHp1. auto.
  - simpl. destruct (peq i id); subst; simpl.
    + constructor. auto.
    + apply IHp1. auto.
Qed.

Lemma transform_partial_program2_link_program
      (lang_src lang_tgt:Language)
      (tf:lang_src.(fundefT)->res lang_tgt.(fundefT))
      (Htf: forall f1 f2 f1' f2'
                   (Hf: globfun_linkable lang_src f1 f2)
                   (H1: tf f1 = OK f1')
                   (H2: tf f2 = OK f2'),
              globfun_linkable lang_tgt f1' f2')
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
  rewrite transform_partial_program2_augment in H1, H2. simpl in *.
  apply transform_partial_augment_program_match in H1. destruct H1 as [[qdefs1 [Hqdefs1 ?]] Hmain1].
  apply transform_partial_augment_program_match in H2. destruct H2 as [[qdefs2 [Hqdefs2 ?]] Hmain2].
  simpl in *. rewrite app_nil_r in *. symmetry in H, H0. subst.
  unfold link_program in *. simpl in *. destruct (Pos.eqb mainp1 mainp2) eqn:Hmainp; [|inv Hp].
  apply Peqb_true_eq in Hmainp. subst. clarify.
  - unfold link_globdef_list in *. clarify.
    eexists. split; eauto. unfold transform_partial_program2. simpl.
    cut (transf_globdefs tf tv (PTree.elements defs0) = OK (PTree.elements defs1)).
    { intro X. rewrite X. auto. }
    apply list_forall2_match_globdef_PTree_unelements in Hqdefs1.
    apply list_forall2_match_globdef_PTree_unelements in Hqdefs2.
    revert defs0 defs1 Hdefs0 Hdefs1 Hqdefs1 Hqdefs2.
    generalize (PTree_unelements p1) (PTree_unelements p2) (PTree_unelements q1) (PTree_unelements q2).
    clear p1 p2 q1 q2. intros p1 p2 q1 q2 p q Hp Hq H1 H2.
    assert (PTree_rel
              (fun (g1 : globdef (fundefT lang_src) (vT lang_src))
                   (g2 : globdef (fundefT lang_tgt) (vT lang_tgt)) =>
                 match_globdef_aux
                   (fun (fd : fundefT lang_src) (tfd : fundefT lang_tgt) =>
                      tf fd = OK tfd)
                   (fun (info : vT lang_src) (tinfo : vT lang_tgt) =>
                      tv info = OK tinfo) g1 g2) p q).
    { constructor. intro.
      eapply gtlink_globdefs in Hp. instantiate (1 := i) in Hp.
      eapply gtlink_globdefs in Hq. instantiate (1 := i) in Hq.
      inv H1. specialize (H i). inv H2. specialize (H0 i).
      revert H H0 Hp Hq.
      destruct (p1 ! i), (p2 ! i), (p ! i), (q1 ! i), (q2 ! i), (q ! i);
        simpl; intros; subst; auto;
        try match goal with | [H: False |- _] => inv H end.
      destruct Hp as [[]|[]], Hq as [[]|[]]; subst; auto.
      - inv H; inv H0; inv H1; inv H3.
        + eapply  Htf in Hv; eauto.
          inv Hv; inv Hv0; simpl in *; clarify.
          rewrite <- H1 in H3. inv H3.
          constructor. rewrite H. f_equal.
          eapply EquivalentType_AtoB_inj; eauto.
        + inv Hv; inv Hv0; simpl in *. subst init0 init ro0 vo0. constructor.
          subst. auto.
      - inv H; inv H0; inv H1; inv H3.
        + eapply  Htf in Hv; eauto.
          inv Hv; inv Hv0; simpl in *; clarify.
          rewrite <- H1 in H3. inv H3.
          constructor. rewrite H2. f_equal.
          eapply EquivalentType_AtoB_inj; eauto.
        + inv Hv; inv Hv0; simpl in *. subst init0 init ro0 vo0. constructor.
          subst. auto.
    }
    clear p1 p2 q1 q2 H1 H2 Hp Hq.
    apply PTree_rel_PTree_elements in H. revert H.
    generalize (PTree.elements p) (PTree.elements q). clear p q.
    induction l; intros l0 X; inv X; simpl; auto.
    destruct a. inv H1.
    + rewrite H4. erewrite IHl; eauto. simpl. auto.
    + unfold transf_globvar. simpl. rewrite H4. simpl. erewrite IHl; eauto. simpl. auto.
  - exfalso. unfold link_globdef_list in *. clarify.
    eapply gflink_globdefs in Hdefs1.
    destruct Hdefs1 as [i [tdef1 [tdef2 [Htdef1 [Htdef2 [Htdefs1 Htdefs2]]]]]].
    eapply gtlink_globdefs in Hdefs0. instantiate (1 := i) in Hdefs0.
    rewrite PTree_guespec in Htdef1. rewrite PTree_guespec in Htdef2.
    rewrite ? PTree_guespec in Hdefs0.
    apply list_forall2_rev in Hqdefs1. apply list_forall2_rev in Hqdefs2.
    exploit (list_forall2_match_globdef_find i (rev p1) (rev q1)); eauto. intro H1.
    exploit (list_forall2_match_globdef_find i (rev p2) (rev q2)); eauto. intro H2.
    unfold option_map in *. clarify.
    unfold ident in *. simpl in *. rewrite Hdefs,Hdefs1 in *. clarify.
    + destruct H1 as [H1 ?]. subst. contradict Htdefs1. inv H1. constructor. eapply Htf; eauto.
    + destruct H1 as [H1 ?]. subst. contradict Htdefs2. inv H1. constructor. eapply Htf; eauto.
    + destruct H1 as [H1 ?]. subst. inv H1.
    + destruct H1 as [H1 ?]. subst. inv H1.
    + destruct H1 as [H1 ?]. subst. inv H1.
    + destruct H1 as [H1 ?]. subst. inv H1.
    + destruct H1 as [H1 ?]. subst. contradict Htdefs1.
      inv H1. inv Hv. simpl in *. subst. constructor. constructor; simpl; auto.
      rewrite H in H0. inv H0. auto.
    + destruct H1 as [H1 ?]. subst. contradict Htdefs2.
      inv H1. inv Hv. simpl in *. subst. constructor. constructor; simpl; auto.
      rewrite H in H0. inv H0. auto.
Qed.
