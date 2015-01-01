(** Well-founded orders. *)

Require Import Arith Relations Max NPeano Omega Program.

Set Implicit Arguments. 
Global Set Bullet Behavior "Strict Subproofs".

Lemma mp: forall P Q: Type, P -> (P -> Q) -> Q.
Proof. intuition. Defined.

Ltac hexploit x := eapply mp; [eapply x|].

Notation rtc := (clos_refl_trans _). (* reflexive transitive closure *)
Notation tc := (clos_trans _). (* transitive closure *)
Hint Immediate rt_step rt_refl t_step.

Lemma tc_rtc: forall X r (a b: X)
    (TC: clos_trans _ r a b),
  clos_refl_trans _ r a b.
Proof.
  intros; induction TC; eauto using rt_trans.
Qed.

Lemma rtc_tc: forall X r (a b: X)
    (RTC: rtc r a b),
  a = b \/ tc r a b.
Proof.
  intros; induction RTC; [| |destruct IHRTC1, IHRTC2]; subst; eauto.
  right; econstructor 2; eauto.
Qed.

Lemma tc_rtc_tc: forall X r (a b c: X)
    (TC: tc r a b)
    (RTC: rtc r b c),
  tc r a c.
Proof.
  intros; induction RTC; eauto using t_trans, t_step.
Qed.

Lemma rtc_tc_tc: forall X r (a b c: X)
    (RTC: rtc r a b)
    (TC: tc r b c),
  tc r a c.
Proof.
  intros; induction RTC; eauto using t_trans, t_step.
Qed.



(** * Definitions. *)

Structure wfo := mkwfo
{ wfo_set :> Type
; wfo_lt : wfo_set -> wfo_set -> Prop
; wfo_wf : well_founded wfo_lt
}.

Inductive gwfu : Type :=
| gwf_zero
| gwf_ord (ord: wfo) (a: ord)
| gwf_sympair (i: gwfu) (j: gwfu)
| gwf_lexpair (i: gwfu) (j: gwfu)
.

Inductive gwfult : gwfu -> gwfu -> Prop :=
| gwflt_zero_ord o a
  : gwfult gwf_zero (gwf_ord o a)
| gwflt_zero_sympair i j
  : gwfult gwf_zero (gwf_sympair i j)
| gwflt_zero_lexpair i j
  : gwfult gwf_zero (gwf_lexpair i j)
| gwflt_ord o a a'
    (LT: wfo_lt o a a')
  : gwfult (gwf_ord o a) (gwf_ord o a')

| gwflt_sympair_width_l i j
  : gwfult i (gwf_sympair i j)
| gwflt_sympair_width_r i j
  : gwfult j (gwf_sympair i j)
| gwflt_sympair_depth_l i i' j
    (LTl: gwfult i i')
  : gwfult (gwf_sympair i j) (gwf_sympair i' j)
| gwflt_sympair_depth_r i j j'
    (LTl: gwfult j j')
  : gwfult (gwf_sympair i j) (gwf_sympair i j')

| gwflt_lexpair_depth_l i i' j j'
    (LT: gwfult i i')
  : gwfult (gwf_lexpair i j) (gwf_lexpair i' j')
| gwflt_lexpair_depth_r i j j'
    (LT: gwfult j j')
  : gwfult (gwf_lexpair i j) (gwf_lexpair i j')
.
Hint Constructors gwfult.

(****
  Stratified GWFs
 ****)

Fixpoint gwfweight (a : gwfu) : nat :=
  match a with
  | gwf_zero => 0
  | gwf_ord _ _ => 0
  | gwf_sympair i j => max (gwfweight i) (gwfweight j)
  | gwf_lexpair i j => max (gwfweight i) (1 + gwfweight j)
  end.

Structure gwf_ (n: nat) := mkgwf
{ gwf_elmt :> gwfu
; gwf_lt : gwfweight gwf_elmt < n
}.

Definition gwf n := gwf_ (S n).

Definition gwflt {n} (a b: gwf n) := gwfult a b.

Definition gwfle {n} (a b : gwf n) : Prop :=
  rtc gwflt a b.
Hint Unfold gwfle.

Program Definition gwfzero {o} : gwf o := 
  mkgwf gwf_zero _.
Next Obligation. omega. Qed.

Definition gwfuadd (i j: gwfu) : gwfu :=
  match i with
  | gwf_zero => j
  | _ => gwf_sympair i j
  end.
Arguments gwfuadd _ _ : simpl nomatch.

Program Definition gwfadd {o} (i j: gwf o) : gwf o :=
  mkgwf (gwfuadd i j) _.
Next Obligation.
  destruct i as [i LTi]; destruct j as [j LTj].
  destruct i; simpl in *; eauto using Nat.max_lub_lt.
Qed.

Program Definition gwfup {o o'} (LE: o <= o') (i: gwf o) : gwf o' :=
  mkgwf i _.
Next Obligation.
  destruct i as [i Lti]; simpl; omega.
Qed.

(** * Properties. *)

Fixpoint gwfsize (a : gwfu) : nat :=
  match a with
  | gwf_zero => 0
  | gwf_ord _ _ => 0
  | gwf_sympair i j => 1 + gwfsize i + gwfsize j
  | gwf_lexpair i _ => 1 + gwfsize i
  end.

Lemma gwfsize_lt: forall a b (LT: gwfult a b),
  gwfsize a <= gwfsize b.
Proof.
  intros; induction LT; simpl in *; eauto; omega.
Qed.

Lemma gwflt_well_founded: forall n,
  well_founded (@gwflt n).
Proof.
  set (gwflt_ := fun n (a b: gwf_ n) => gwfult a b).
  cut (forall n, well_founded (gwflt_ n)).
  { eauto. }

  red; induction n; [repeat intro; destruct a; omega|].
  cut (forall m (a : gwf_ (S n)) (LEV: gwfsize a < m), Acc (gwflt_ (S n)) a).
  { repeat intro; eauto. }

  induction m; [intros; omega|].
  intros; destruct a as [a LT].
  destruct a as [| |a b|a b].

  { econstructor; intros; red in H; simpl in *; dependent destruction H. }

  { assert (X:= ord.(wfo_wf) a).
    induction X as [a HA HP].
    econstructor; intros x Rx; red in  Rx; simpl in *.
    destruct x as [x LEVx]; simpl in *.
    dependent destruction Rx; eauto.
    econstructor; intros; red in  H; dependent destruction H.
  } 

  { simpl in *; assert (LTan: gwfweight a < S n). 
    { assert (X := le_max_l (gwfweight a) (gwfweight b)); omega. }
    set (aa := mkgwf a LTan).
    change a with (gwf_elmt aa) in LT, LEV |- *.
    clearbody aa; clear a LTan.

    hexploit (IHm aa); [omega| intros ACCa].
    revert b LT LEV; induction ACCa as [a ACCa ACCa'].

    intros; assert (LTbn: gwfweight b < S n). 
    { assert (X := le_max_r (gwfweight a) (gwfweight b)); omega. }
    set (bb := mkgwf b LTbn).
    change b with (gwf_elmt bb) in LT, LEV |- *.
    clearbody bb; clear b LTbn.

    hexploit (IHm bb); [omega| intros ACCb].
    revert LT LEV; induction ACCb as [b ACCb ACCb'].

    intros; econstructor; intros c LTc.
    red in  LTc; dependent destruction LTc; destruct c as [c LTc']; simpl in *; subst; simpl in *; eauto using Acc_intro.
    - econstructor; intros; red in  H; dependent destruction H.
    - assert (LTi: gwfweight i < S n).
      { assert (X := le_max_l (gwfweight i) (gwfweight b)); omega. }
      apply (ACCa' (mkgwf i LTi) LTc b).
      simpl; apply gwfsize_lt in LTc; omega.
    - assert (LTj: gwfweight j < S n).
      { assert (X := le_max_r (gwfweight a) (gwfweight j)); omega. }
      apply (ACCb' (mkgwf j LTj) LTc).
      simpl; apply gwfsize_lt in LTc; omega.
  }
  { simpl in *; assert (LTan: gwfweight a < S n). 
    { assert (X := le_max_l (gwfweight a) (S (gwfweight b))); omega. }
    set (aa := mkgwf a LTan).
    change a with (gwf_elmt aa) in LT, LEV |- *.
    clearbody aa; clear a LTan.

    hexploit (IHm aa); [omega| intros ACCa].
    revert b LT LEV; induction ACCa as [a ACCa ACCa'].

    intros; assert (LTbn: gwfweight b < n). 
    { assert (X := le_max_r (gwfweight a) (S (gwfweight b))); omega. }
    set (bb := mkgwf b LTbn).
    change b with (gwf_elmt bb) in LT, LEV |- *.
    clearbody bb; clear b LTbn.

    assert (ACCb := IHn bb).
    revert LT; induction ACCb as [b ACCb ACCb'].

    intros; econstructor; intros c LTc.
    red in  LTc; dependent destruction LTc; destruct c as [c LTc']; simpl in *; subst; simpl in *; eauto using Acc_intro.
    - econstructor; intros; red in  H; dependent destruction H.
    - assert (LTi: gwfweight i < S n).
      { assert (X := le_max_l (gwfweight i) (S (gwfweight j))); omega. }
      apply (ACCa' (mkgwf i LTi) LTc j).
      simpl; apply gwfsize_lt in LTc; omega.
    - assert (LTj: gwfweight j < n). 
      { assert (X := le_max_r (gwfweight a) (S (gwfweight j))); omega. }
      apply (ACCb' (mkgwf j LTj)); eauto.
  }
Qed.

Lemma gwf_eq: forall o (i j: gwf o)
    (EQ: gwf_elmt i = gwf_elmt j),
  i = j.
Proof.
  intros; destruct i as [i LTi]; destruct j as [j LTj].
  simpl in *; subst; rewrite (proof_irrelevance _ LTi LTj); auto.
Qed.

(* Lemma gwf_lexpair_lt1: forall ia ia' ib ib' *)
(*     (LT: tc gwfult ia ia'), *)
(*   tc gwfult (gwf_lexpair ia ib) (gwf_lexpair ia' ib'). *)
(* Proof.  *)
(*   clear; intros; depgen ib'; induction LT; i. *)
(*   - apply t_step; destruct x, y, ib; simpl in *; eauto; dependent destruction H. *)
(*   - eapply t_trans; eauto. *)
(* Qed. *)

(* Lemma gwf_lexpair_lt2: forall ia ib ib' *)
(*     (LT: tc gwfult ib ib'), *)
(*   tc gwfult (gwf_lexpair ia ib) (gwf_lexpair ia ib'). *)
(* Proof.  *)
(*   clear; intros; induction LT; i. *)
(*   - apply t_step; destruct x, y, ia; simpl in *; eauto; dependent destruction H. *)
(*   - eapply t_trans; eauto. *)
(* Qed. *)

Definition gwf_lex o (ia ib: gwf o) : gwf (S o).
  refine {| gwf_elmt := gwf_lexpair ia ib |}.
  hexploit (gwf_lt ia); hexploit (gwf_lt ib).
  simpl; apply max_case; omega. 
Defined.
(* TODO ideally should call this gwf_lexpair and the constructor gwfu_lexpair *)

Lemma gwf_lex_lt1: forall o (ia ia' ib ib': gwf o)
    (LT: tc gwflt ia ia'),
  tc gwflt (gwf_lex ia ib) (gwf_lex ia' ib').
Proof. 
  clear; intros; revert ib ib'; induction LT; [econstructor 1|econstructor 2]; repeat red; simpl in *; eauto.
Grab Existential Variables.
  eauto.
Qed.

Lemma gwf_lex_lt2: forall o (ia ib ib': gwf o)
    (LT: tc gwflt ib ib'),
  tc gwflt (gwf_lex ia ib) (gwf_lex ia ib').
Proof. 
  clear; intros; revert ia; induction LT; [econstructor 1|econstructor 2]; repeat red; simpl in *; eauto.
Qed.



(* Lemma gwfadd_lt1: forall ia ia' ib *)
(*     (LT: tc gwflt ia ia'), *)
(*   tc gwflt (gwfadd ia ib) (gwfadd ia' ib). *)
(* Proof.  *)
(*   intros; induction LT. *)
(*   - apply t_step; destruct x, y, ib; simpl in *; eauto; dependent destruction H. *)
(*   - eapply t_trans; eauto. *)
(* Qed. *)

Lemma gwfadd_lt1: forall o (ia ia' ib: gwf o)
    (LT: tc gwflt ia ia'),
  tc gwflt (gwfadd ia ib) (gwfadd ia' ib).
Proof. 
  intros; induction LT.
  - apply t_step; destruct x as [x LTx]; destruct y as [y LTy]; destruct ib as [ib LTib].
    red; red in  H; simpl in *. 
    destruct x, y; simpl; eauto; dependent destruction H. 
  - eapply t_trans; eauto.
Qed.

(* Lemma gwfadd_lt2: forall ia ib ib' *)
(*     (LT: tc gwflt ib ib'), *)
(*   tc gwflt (gwfadd ia ib) (gwfadd ia ib'). *)
(* Proof.  *)
(*   intros; induction LT. *)
(*   - apply t_step; destruct x, y, ia; simpl in *; eauto; dependent destruction H. *)
(*   - eapply t_trans; eauto. *)
(* Qed. *)

Lemma gwfadd_lt2: forall o (ia ib ib': gwf o)
    (LT: tc gwflt ib ib'),
  tc gwflt (gwfadd ia ib) (gwfadd ia ib').
Proof. 
  intros; induction LT.
  - apply t_step; destruct x as [x LTx]; destruct y as [y LTy]; destruct ia as [ia LTia].
    red; red in  H; simpl in *. 
    destruct ia; simpl; eauto; dependent destruction H. 
  - eapply t_trans; eauto.
Qed.

Lemma gwfadd_le1: forall o (i j: gwf o),
  gwfle i (gwfadd i j).
Proof.
  intros; destruct i as [i LTi]; destruct i; red; simpl; try (apply rt_step; red; simpl; eauto; fail).
  unfold gwfadd; simpl.
  destruct j as [j LTj]. 
  destruct j; simpl; try (apply rt_step; red; simpl; eauto; fail).
  setoid_rewrite (proof_irrelevance _ _ LTi); eauto.
Qed.

Lemma gwfadd_le2: forall o (i j: gwf o),
  gwfle j (gwfadd i j).
Proof.
  intros; destruct i as [i LTi]; destruct i; red; simpl; try (apply rt_step; red; simpl; eauto; fail). 
  unfold gwfadd; simpl; destruct j as [j LTj].
  setoid_rewrite (proof_irrelevance _ _ LTj); eauto.
Qed.

Lemma gwfadd_zero: forall o (i: gwf o),
  gwfadd gwfzero i = i.
Proof. 
  intros; apply gwf_eq; auto.
Qed.

Lemma gwfle_zero: forall o (i: gwf o),
  gwfle gwfzero i.
Proof.
  intros; rewrite <- (gwfadd_zero i); eauto using gwfadd_le1.
Qed.

Lemma gwfle_trans: forall o (i i' i'' : gwf o)
    (LEA: gwfle i i')
    (LEB: gwfle i' i''),
  gwfle i i''.
Proof.
  intros; eapply rt_trans; eauto.
Qed.

Lemma gwflt_tc_split: forall o (i i': gwf o)
    (LT: tc gwflt i i'),
  exists im, gwfle i im /\ gwflt im i'.
Proof.
  intros; induction LT; eauto.
  destruct IHLT1 as [? [? ?]].
  destruct IHLT2 as [im [? ?]].
  exists im; split; eauto using gwfle_trans.
Qed.


(** [gwfle_n n o o'] means that [o'] can be decreased at least [n] times
    before reaching [o].
*)
Inductive gwfle_n o : nat -> gwf o -> gwf o -> Prop :=
| gwfle_n_Z i j (LE: gwfle i j)
  : gwfle_n O i j
| gwfle_n_S n i j k (GLE: gwfle_n n i j) (LT: tc gwflt j k)
  : gwfle_n (S n) i k
.
Hint Constructors gwfle_n.

Lemma gwfle_n_lt: forall o n (i i': gwf o)
    (LE: gwfle_n (S n) i i'),
  tc gwflt i i'.
Proof.
  induction n; intros; dependent destruction LE.
  - dependent destruction LE; simpl in LE; eauto using rtc_tc_tc.
  - econstructor 2; [|eauto using IHn]; eauto.
Qed.

Program Definition gwfnat {o} (n: nat) : gwf o :=
  mkgwf (gwf_ord (mkwfo lt_wf) n) _.
Next Obligation. omega. Qed.    (* TODO move up *)

Lemma gwfle_n_add_S: forall o n (i: gwf o),
  gwfle_n (S n) i (gwfadd (gwfnat n) i).
Proof.
  intros; destruct i as [i LTi].
  revert i LTi; induction n.
  - intros; econstructor.
    + econstructor; apply rt_refl.
    + apply t_step; red; simpl; eauto.
  - intros; econstructor; eauto.
    apply t_step; red; simpl.
    apply gwflt_sympair_depth_l.
    apply gwflt_ord; simpl; omega.
Qed.

Lemma gwfle_n_add: forall o n (i: gwf o),
  gwfle_n n i (gwfadd (gwfnat n) i).
Proof.
  intros; hexploit (gwfle_n_add_S n i); eauto; intros.
  do 2 dependent destruction X; [econstructor 1|econstructor 2]; eauto using rt_trans, tc_rtc, t_trans.
Qed.

(* TODO rename (D) *)
Lemma gwfle_n_S': forall o n (i i': gwf o)
    (LE: gwfle_n (S n) i i'),
  exists o,
    tc gwflt i o /\
    gwfle_n n o i'.
Proof.
  induction n; intros; dependent destruction LE.
  - dependent destruction LE; eauto 10 using rtc_tc_tc.
  - hexploit IHn; eauto; intros; destruct X as [? [? ?]]; eauto.
Qed.

Lemma gwfle_n_S'': forall o n (i i': gwf o)
    (LE: gwfle_n (S n) i i'),
   gwfle_n n i i'.
Proof.
  intros; do 2 dependent destruction LE; [econstructor 1|]; eauto using rt_trans, tc_rtc, t_trans.
Qed.

Lemma gwfle_n_gwfle: forall o n (i i' i'': gwf o)
   (GLE: gwfle_n n i i')
   (LE: gwfle i' i''),
 gwfle_n n i i''.
Proof.
  intros; dependent destruction GLE; [econstructor 1|econstructor 2].
  - econstructor 3; eauto.
  - eapply rtc_tc in LE; destruct LE; subst; eauto.
  - eauto using tc_rtc_tc.
Qed.

Lemma gwfle_n_anti: forall o m n (i i': gwf o)
    (GLE: gwfle_n m i i')
    (LE: n <= m),
  gwfle_n n i i'.
Proof.
  intros; revert o i i' GLE; induction LE; [auto|].
  intros; apply IHLE; auto using gwfle_n_S''.
Qed.

(* TODO rename *)
Lemma gwfle_n_S_rev: forall o (i j: gwf o) n k
    (LT: tc gwflt i j)
    (GLE: gwfle_n n j k),
  gwfle_n (S n) i k.
Proof.
  intros; revert i LT; induction GLE; intros.
  - econstructor; eauto using tc_rtc_tc.
  - eauto.
Qed.

Lemma gwfle_n_plus: forall o n na nb (i i': gwf o)
    (GLE: gwfle_n n i i')
    (E: n = na + nb),
  exists ii,
    gwfle_n na i ii /\
    gwfle_n nb ii i'.
Proof.
  intros o n na; revert o n; induction na; simpl; intros; subst.
  - exists i; eauto.
  - apply gwfle_n_S' in GLE; destruct GLE as [o0 [LT LE]].
    eapply IHna in LE; [destruct LE as [ii [? ? ]] | ]; eauto.
    exists ii; eauto; split; eauto using gwfle_n_S_rev.
Qed.
