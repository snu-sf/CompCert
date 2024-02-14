(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU Lesser General Public License as        *)
(*  published by the Free Software Foundation, either version 2.1 of   *)
(*  the License, or  (at your option) any later version.               *)
(*  This file is also distributed under the terms of the               *)
(*  INRIA Non-Commercial License Agreement.                            *)
(*                                                                     *)
(* *********************************************************************)

(** Stack environments are a component of the dynamic semantics of
  all languages involved in the compiler.  A stack environment
  maps identifier names (names of stack variables)
  to the corresponding memory addresses and block sizes.

  Stack environments, at the beginning of function execution, are built
  from the program of interest. A distinct memory address is assigned to
  each stack variable of a function. For each stack variable, a memory
  block is allocated and associated to the name of the variable.

  These stack environments are implemented to handle stack variables
  independent from executions of other variables. *)

Require Import Axioms Coqlib Errors Maps AST Linking.
Require Import Integers Floats Values Memory.

Declare Scope pair_scope.
Notation "s #1" := (fst s) (at level 9, format "s '#1'") : pair_scope.
Notation "s #2" := (snd s) (at level 9, format "s '#2'") : pair_scope.
Local Open Scope pair_scope.
Local Open Scope error_monad_scope.

Set Implicit Arguments.

(* Types for moving ids and addresses in stack environments *)

Definition movid: Type := ident -> ident.
Definition flat_mid: movid := fun id => id.
Definition movaddr: Type := ident -> Z.
Definition flat_maddr: movaddr := fun id => 0.

(** * Two representations of stack environments *)

Module Venv.

(** ** Stack environments as a map of blocks *)

(** [Venv.t] is an expression of variable blocks.
 [vars]: A map associating a variable id to a block.
 [baseblock]: A baseline block. Actual stack blocks are allocated above this. The block is allocated with zero size.
 [nextblock]: A block that will be allocated when the next variable is allocated. *)

Record t: Type := mkvenv {
  vars: PTree.t block;
  defs: PTree.t (ident * Z);
  baseblock: block;
  nextblock: block;
  (** Properties *)
  vars_range: forall id b, PTree.get id vars = Some b -> Plt baseblock b /\ Plt b nextblock;
  defs_range: forall b id_sz, PTree.get b defs = Some id_sz -> Plt baseblock b /\ Plt b nextblock;
  checkpoint_order: Plt baseblock nextblock;
}.

(** ** Lookup functions *)

(** [find_var ve id] returns the block associated with the given name, if any *)

Definition find_var (ve: Venv.t) (id: ident) : option block :=
  PTree.get (id) (vars ve).

(** [find_def ve b] returns the variable definition associated with the given address. *)

Definition find_def (ve: t) (b: block) : option (ident * Z) :=
  PTree.get b (defs ve).

Definition valid_block (ve: Venv.t) (b: block) :=
  Ple (baseblock ve) b /\ Plt b (nextblock ve).

Lemma gt_nextblock_one:
  forall ve, Plt 1%positive (nextblock ve).
Proof.
  intros. assert (Ple 1%positive (baseblock ve)). extlia.
  pose proof (checkpoint_order ve).
  extlia.
Qed.

Definition lastblock (ve: t) := Pos.pred (nextblock ve).

Lemma succ_nextblock_lastblock:
  forall ve, Pos.succ (lastblock ve) = (nextblock ve).
Proof.
  intros.
  pose proof (gt_nextblock_one ve).
  pose proof (checkpoint_order ve).
  unfold lastblock.
  extlia.
Qed.

Lemma lastblock_valid:
  forall ve, valid_block ve (lastblock ve).
Proof.
  intros.
  pose proof (gt_nextblock_one ve).
  pose proof (checkpoint_order ve).
  unfold valid_block, lastblock; extlia.
Qed.

(** ** Constructing the stack blocks *)

Program Definition add_var (ve: t) (id_sz: (ident * Z)) :=
  @mkvenv
    (PTree.set id_sz#1 ve.(nextblock) ve.(vars))
    (PTree.set ve.(nextblock) id_sz ve.(defs))
    ve.(baseblock)
    (Pos.succ ve.(nextblock))
    _ _ _.
Next Obligation.
  induction ve; simpl in *.
  rewrite PTree.gsspec in H. destruct (peq id i). inv H; extlia.
  apply vars_range0 in H. extlia.
Qed.
Next Obligation.
  induction ve; simpl in *.
  rewrite PTree.gsspec in H. destruct (peq b nextblock0).
  inv H. extlia.
  apply defs_range0 in H. extlia.
Qed.
Next Obligation.
  induction ve; simpl in *; extlia.
Qed.

Program Definition add_vars (ve: t) (vl: list (ident * Z)) :=
  List.fold_left add_var vl ve.

Lemma add_vars_app:
  forall vl1 vl2 ve,
  add_vars ve (vl1 ++ vl2) = add_vars (add_vars ve vl1) vl2.
Proof.
  intros. apply fold_left_app.
Qed.

Program Definition empty_venv (base: block) :=
  @mkvenv (PTree.empty _) (PTree.empty _) base (Pos.succ base) _ _ _.
Next Obligation.
  extlia.
Qed.

Section VARENV_PRINCIPLES.

Definition advance_next (vl: list (ident * Z)) (x: positive) :=
  List.fold_left (fun n sz => Pos.succ n) vl x.

End VARENV_PRINCIPLES.

Section INITMEM.

Definition alloc_var (m: mem) (sz: Z) :=
  Mem.alloc m 0 sz.

Definition alloc_baseblock (m: mem) := alloc_var m 0.

Fixpoint alloc_vars (m: mem) (vl: list (ident * Z)) :=
  match vl with
  | nil => m
  | (id, sz) :: vl' =>
      match alloc_var m sz with
      | (m', b) => alloc_vars m' vl'
      end
  end.

Lemma alloc_vars_app: forall vl1 vl2 m m1,
  alloc_vars m vl1 = m1 ->
  alloc_vars m1 vl2 = alloc_vars m (vl1 ++ vl2).
Proof.
  induction vl1.
  simpl. intros. inversion H; subst. auto.
  simpl. intros. destruct a. destruct (alloc_var m z); eauto.
Qed.

Remark alloc_var_nextblock:
  forall v m m' b,
  alloc_var m v = (m', b) ->
  Mem.nextblock m' = Pos.succ(Mem.nextblock m).
Proof.
  unfold alloc_var. intros.
  erewrite Mem.nextblock_alloc; eauto.
Qed.

Remark alloc_vars_nextblock:
  forall vl m m',
  alloc_vars m vl = m' ->
  Mem.nextblock m' = advance_next vl (Mem.nextblock m).
Proof.
  induction vl; simpl; intros.
  congruence.
  destruct a. destruct (alloc_var m z) eqn:?.
  erewrite IHvl; eauto. erewrite alloc_var_nextblock; eauto.
Qed.

Remark alloc_var_perm:
  forall k prm b b' q sz m m',
  alloc_var m sz = (m', b) ->
  Mem.valid_block m b' ->
  (Mem.perm m b' q k prm <-> Mem.perm m' b' q k prm).
Proof.
  intros.
  assert (b' <> b). apply Mem.valid_not_valid_diff with m; eauto with mem.
  split; intros.
  eapply Mem.perm_alloc_1 in H; eauto.
  eapply Mem.perm_alloc_4; eauto.
Qed.

Remark alloc_vars_perm:
  forall k prm b' q vl m m',
  alloc_vars m vl = m' ->
  Mem.valid_block m b' ->
  (Mem.perm m b' q k prm <-> Mem.perm m' b' q k prm).
Proof.
  induction vl.
  simpl; intros. inv H. tauto.
  simpl; intros. destruct a; destruct (alloc_var m z) as [m1 b1] eqn:?; try discriminate.
  erewrite alloc_var_perm; eauto. eapply IHvl; eauto.
  unfold Mem.valid_block in *. erewrite alloc_var_nextblock; eauto.
  apply Plt_trans_succ; auto.
Qed.

Remark alloc_var_unchanged:
  forall (P: block -> Z -> Prop) m sz m' b,
  alloc_var m sz = (m', b) ->
  Mem.unchanged_on P m m'.
Proof.
  intros. destruct (alloc_var m sz) eqn:?. inv H.
  set (Q := fun b' (ofs: Z) => b' <> b).
  apply Mem.unchanged_on_implies with Q.
  apply Mem.unchanged_on_trans with m'.
  eapply Mem.alloc_unchanged_on; eauto.
  apply Mem.unchanged_on_refl.
  intros; red. apply Mem.valid_not_valid_diff with m; eauto with mem.
Qed.

Remark alloc_vars_unchanged:
  forall (P: block -> Z -> Prop) vl m m',
  alloc_vars m vl = m' ->
  Mem.unchanged_on P m m'.
Proof.
  induction vl; simpl; intros.
- inv H. apply Mem.unchanged_on_refl.
- destruct a; destruct (alloc_var m z) eqn:?; try discriminate.
  apply Mem.unchanged_on_trans with m0.
  eapply alloc_var_unchanged; eauto.
  apply IHvl; auto.
Qed.

Definition vars_initialized (ve: t) (m: mem) :=
  forall b id_sz,
  find_def ve b = Some id_sz ->
  Mem.range_perm m b 0 id_sz#2 Cur Freeable /\
  (forall ofs k p, Mem.perm m b ofs k p -> 0 <= ofs < id_sz#2 /\ perm_order Freeable p).

Lemma alloc_var_initialized:
  forall ve m id sz m' b,
  nextblock ve = Mem.nextblock m ->
  alloc_var m sz = (m', b) ->
  vars_initialized ve m ->
     vars_initialized (add_var ve (id, sz)) m'
  /\ nextblock (add_var ve (id, sz)) = Mem.nextblock m'.
Proof.
  intros.
  exploit alloc_var_nextblock; eauto. intros NB. split.
  - red; intros. unfold find_def in H2; simpl in H2.
    rewrite PTree.gsspec in H2. destruct (peq b0 (nextblock ve)).
    + inv H2. exploit Mem.alloc_result; eauto. intros RES.
      replace (nextblock ve) with b by congruence.
      split. red; intros. eapply Mem.perm_alloc_2; eauto.
      intros. split. eapply Mem.perm_alloc_3; eauto. econstructor.
    + assert (U: Mem.unchanged_on (fun _ _ => True) m m') by (eapply alloc_var_unchanged; eauto).
      assert (VALID: Mem.valid_block m b0).
      { red. rewrite <- H. eapply defs_range; eauto. }
      exploit H1; eauto.
      intros (A & B). split.
      red; intros. eapply Mem.perm_unchanged_on; eauto. exact I.
      intros. eapply B. eapply Mem.perm_unchanged_on_2; eauto. exact I.
- simpl. congruence.
Qed.

Lemma alloc_vars_initialized:
  forall vl ve m m',
  alloc_vars m vl = m' ->
  nextblock ve = Mem.nextblock m ->
  vars_initialized ve m ->
  vars_initialized (add_vars ve vl) m'.
Proof.
  induction vl; simpl; intros.
- inv H; auto.
- destruct a as [id sz]. destruct (alloc_var m sz) eqn:?; try discriminate.
  exploit alloc_var_initialized; eauto. intros [P Q].
  eapply IHvl; eauto.
Qed.

End INITMEM.

Section MEMORY.

Theorem alloc_baseblock_extends:
  forall m1 m2 m1' b,
  Mem.extends m1 m2 ->
  alloc_baseblock m1 = (m1', b) ->
  exists m2', alloc_baseblock m2 = (m2', b) /\ Mem.extends m1' m2'.
Proof.
  unfold alloc_baseblock. intros.
  apply (Mem.alloc_extends m1 m2 0 0 b m1' 0 0) in H0 as [m2' H0]; auto; try lia.
  exists m2'; auto.
Qed.

Theorem alloc_vars_extends:
  forall l m1 m2 m1',
  Mem.extends m1 m2 ->
  alloc_vars m1 l = m1' ->
  exists m2', alloc_vars m2 l = m2'
  /\ Mem.extends m1' m2'.
Proof.
  induction l; simpl; intros.
  - exists m2. inv H0; auto.
  - destruct a as [id sz].
    destruct (alloc_var m1 sz) as [m11 b1] eqn:E1.
    destruct (Mem.alloc_extends m1 m2 0 sz b1 m11 0 sz) as [m22 H2]; auto; try lia.
    destruct H2 as [E2 H1].
    unfold alloc_vars, alloc_var. rewrite E2.
    apply IHl with (m1 := m11); auto.
Qed.

Section INJECTION.

Definition meminj_varenv (ve1 ve2: Venv.t) (f: meminj) (mid: movid) (maddr: movaddr): Prop :=
  forall id1 b1, find_var ve1 id1 = Some b1 ->
  exists id2 b2 delta, find_var ve2 id2 = Some b2 /\ f b1 = Some (b2, delta)
                  /\ mid id1 = id2 /\ maddr id2 = delta.

End INJECTION.

(** List of blocks mentioned in environments, with low and high bounds *)

Fixpoint blocks_of_venv
             (ve: Venv.t)
             (vl: list (ident * Z)) :=
  match vl with
  | nil => nil
  | (id, sz) :: vl => match find_var ve id with
                    | Some b => (b, 0, sz) :: blocks_of_venv ve vl
                    | None => blocks_of_venv ve vl
                    end
  end.

End MEMORY.

Program Definition varenv (m: mem) (vl: list (ident * Z)) :=
  let (m', base) := alloc_baseblock m in
  (alloc_vars m' vl, add_vars (empty_venv base) vl).

Theorem varenv_extends:
  forall l m1 m2 m1' ve,
  Mem.extends m1 m2 ->
  varenv m1 l = (m1', ve) ->
  exists m2', varenv m2 l = (m2', ve) /\ Mem.extends m1' m2'.
Proof.
  unfold varenv; simpl.
  intros.
  case_eq (alloc_baseblock m1); intros m11 b1 ALLOC1.
  case_eq (alloc_baseblock m2); intros m22 b2 ALLOC2.
  rewrite ALLOC1 in H0.

  apply alloc_baseblock_extends with (m1' := m11) (b := b1) in H as BASE; auto.
  destruct BASE as [m22' BASE]. rewrite ALLOC2 in BASE. destruct BASE as [EQ EXT].
  inversion EQ. rewrite <- H2 in *.

  apply alloc_vars_extends with (l := l) (m1' := m1') in EXT as [m2' AVAR].
  destruct AVAR as [AVAR1 AVAR2].
  exists m2'. split; auto.
  rewrite AVAR1; auto.
  inversion H0. auto.
  inversion H0. auto.
Qed.

End Venv.

Module Stenv.

Section STENV.

(** The type of stack environments expressed as blocks, variable injection, and shift offset. *)

Record t: Type := mkstenv {
  stenv_vars: Venv.t;
  stenv_mid: movid;
  stenv_maddr: movaddr;
}.

Program Definition of_venv (ve: Venv.t) (mid: movid) (maddr: movaddr) :=
  @mkstenv ve mid maddr.

(** [move_id ste id] returns a new id of id mapped by stenv_mid of stenv. *)

Definition move_id (ste: t) (id: ident) := (stenv_mid ste) id.

(** [moev_addr ste id] returns an offset of id that points to the variable address. *)

Definition move_addr (ste: t) (id: ident) := Ptrofs.repr ((stenv_maddr ste) id).

(** ** Lookup functions *)

(** [var_address ste id ofs] returns a pointer into the block associated
  with [id], at byte offset [ofs].  [Vundef] is returned if no block is associated to [id]. *)

Definition var_address (ste: t) (id: ident) (ofs: ptrofs) : val :=
  match Venv.find_var (stenv_vars ste) (move_id ste id) with
  | Some b => Val.offset_ptr (Vptr b (move_addr ste (move_id ste id))) ofs
  | None => Vundef
  end.

Lemma address_find_var:
  forall ve mid maddr id b ofs1 ofs2, var_address (of_venv ve mid maddr) id ofs1 = Vptr b ofs2 ->
  Venv.find_var ve (mid id) = Some b.
Proof.
  unfold var_address; intros; simpl in *.
  destruct (Venv.find_var ve (mid id)); inv H; auto.
Qed.

(** ** Properties of the operations over stack environments *)

Theorem shift_var_address:
  forall ste id ofs delta,
  var_address ste id (Ptrofs.add ofs delta) = Val.offset_ptr (var_address ste id ofs) delta.
Proof.
  intros. unfold var_address, Val.offset_ptr. destruct (Venv.find_var _ _); auto.
  rewrite Ptrofs.add_assoc; rewrite Ptrofs.add_commut with (y := delta); auto.
Qed.

Theorem shift_var_address_32:
  forall ste id ofs n,
  Archi.ptr64 = false ->
  var_address ste id (Ptrofs.add ofs (Ptrofs.of_int n)) = Val.add (var_address ste id ofs) (Vint n).
Proof.
  intros. unfold var_address. destruct (Venv.find_var _ _).
  - unfold Val.add; rewrite H; simpl. rewrite Ptrofs.add_assoc; auto.
  - auto.
Qed.

Theorem shift_var_address_64:
  forall ste id ofs n,
  Archi.ptr64 = true ->
  var_address ste id (Ptrofs.add ofs (Ptrofs.of_int64 n)) = Val.addl (var_address ste id ofs) (Vlong n).
Proof.
  intros. unfold var_address. destruct (Venv.find_var _ _).
  - unfold Val.addl; rewrite H; simpl. rewrite Ptrofs.add_assoc; auto.
  - auto.
Qed.

End STENV.

End Stenv.
