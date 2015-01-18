Require Import RelationClasses.
Require Import Coqlib.
Require Import Maps Maps_linker.
Require Import Compopts.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Events.
Require Import Lattice.
Require Import Kildall.
Require Import Registers.
Require Import Op.
Require Import ValueDomain.
Require Import ValueAOp.
Require Import Liveness.
Require Import ValueAnalysis.
Require Import Language Linker Linkeq.
Require Import RTL.

Set Implicit Arguments.

Ltac clarify := simpl in *; fold ident fundef in *.

Lemma program_linkeq_romem_le
      prog fprog
      (Hlinkeq: program_linkeq Language_RTL prog fprog):
  PTree_le (romem_for_program prog) (romem_for_program fprog).
Proof.
  unfold romem_for_program. rewrite <- ? fold_left_rev_right.
  constructor. intro b.
  destruct Hlinkeq as [Hdefs _]. specialize (Hdefs b).
  rewrite ? PTree_guespec in Hdefs.
  revert b Hdefs. clarify.
  generalize (@rev (prod ident _) (prog_defs fprog)) as l2.
  generalize (@rev (prod ident _) (prog_defs prog)) as l1.
  clear prog fprog.
  induction l1; intros l2 b H ab Hab; simpl in *.
  { rewrite PTree.gempty in Hab. inv Hab. }
  destruct a. simpl in Hab.
  destruct g.
  { rewrite PTree.grspec in Hab.
    destruct (PTree.elt_eq b i); inv Hab. rewrite H1.
    apply IHl1; auto. intros.
    exploit H; eauto.
    simpl in *. destruct (peq b i); subst; try (contradict n; auto; fail).
    simpl in *. auto.
  }
  { match goal with
      | [H: (if ?b then _ else _) ! _ = _ |- _] =>
        destruct b eqn:Hb; InvBooleans
    end.
    { rewrite PTree.gsspec in Hab. destruct (peq b i); subst.
      { inv Hab. exploit H; eauto.
        { simpl. destruct (peq i i); subst; try (contradict n; auto; fail).
          simpl. eauto.
        }
        intros [defs2 [Hdefs2 Hsim]].
        inv Hsim. inv Hv.
        { revert Hdefs2. induction l2; simpl; intro X; inv X.
          destruct a. simpl in *. destruct (peq i i0); subst; simpl in *.
          { inv H4. rewrite H2. rewrite H3. rewrite H1. simpl.
            rewrite PTree.gss. auto.
          }
          { destruct g.
            { rewrite PTree.gro; auto. }
            { match goal with
                | [|- (if ?b then _ else _) ! _ = _] =>
                  destruct b
              end.
              { rewrite PTree.gso; auto. }
              { rewrite PTree.gro; auto. }
            }
          }
        }
        { inv H0. clarify. rewrite Hinit in H1. inv H1. }
      }
      { apply IHl1; auto. intros.
        exploit H; eauto.
        simpl in *. destruct (peq b i); subst; try (contradict n; auto; fail).
        simpl in *. auto.
      }
    }
    { rewrite PTree.grspec in Hab.
      destruct (PTree.elt_eq b i); inv Hab. rewrite H1.
      apply IHl1; auto. intros.
      exploit H; eauto.
      simpl in *. destruct (peq b i); subst; try (contradict n; auto; fail).
      simpl in *. auto.
    }
  }
Qed.

(** ** Semantic invariant *)

Section SOUNDNESS.

Variable prog: program.

Let ge : genv := Genv.globalenv prog.

Section PAST.

Variable (rm:romem).

Inductive sound_stack: block_classification -> list stackframe -> mem -> block -> Prop :=
  | sound_stack_nil: forall bc m bound,
      sound_stack bc nil m bound
  | sound_stack_public_call:
      forall (bc: block_classification) res f sp pc e stk m bound bc' bound' ae
        (STK: sound_stack bc' stk m sp)
        (INCR: Ple bound' bound)
        (BELOW: bc_below bc' bound')
        (SP: bc sp = BCother)
        (SP': bc' sp = BCstack)
        (SAME: forall b, Plt b bound' -> b <> sp -> bc b = bc' b)
        (GE: genv_match bc' ge)
        (AN: VA.ge (analyze rm f)!!pc (VA.State (AE.set res Vtop ae) mafter_public_call))
        (EM: ematch bc' e ae),
      sound_stack bc (Stackframe res f (Vptr sp Int.zero) pc e :: stk) m bound
  | sound_stack_private_call:
     forall (bc: block_classification) res f sp pc e stk m bound bc' bound' ae am
        (STK: sound_stack bc' stk m sp)
        (INCR: Ple bound' bound)
        (BELOW: bc_below bc' bound')
        (SP: bc sp = BCinvalid)
        (SP': bc' sp = BCstack)
        (SAME: forall b, Plt b bound' -> b <> sp -> bc b = bc' b)
        (GE: genv_match bc' ge)
        (AN: VA.ge (analyze rm f)!!pc (VA.State (AE.set res (Ifptr Nonstack) ae) (mafter_private_call am)))
        (EM: ematch bc' e ae)
        (CONTENTS: bmatch bc' m sp am.(am_stack)),
      sound_stack bc (Stackframe res f (Vptr sp Int.zero) pc e :: stk) m bound.

Inductive sound_state: state -> Prop :=
  | sound_regular_state:
      forall s f sp pc e m ae am bc
        (STK: sound_stack bc s m sp)
        (AN: (analyze rm f)!!pc = VA.State ae am)
        (EM: ematch bc e ae)
        (RO: romatch bc m rm)
        (MM: mmatch bc m am)
        (GE: genv_match bc ge)
        (SP: bc sp = BCstack),
      sound_state (State s f (Vptr sp Int.zero) pc e m)
  | sound_call_state:
      forall s fd args m bc
        (STK: sound_stack bc s m (Mem.nextblock m))
        (ARGS: forall v, In v args -> vmatch bc v Vtop)
        (RO: romatch bc m rm)
        (MM: mmatch bc m mtop)
        (GE: genv_match bc ge)
        (NOSTK: bc_nostack bc),
      sound_state (Callstate s fd args m)
  | sound_return_state:
      forall s v m bc
        (STK: sound_stack bc s m (Mem.nextblock m))
        (RES: vmatch bc v Vtop)
        (RO: romatch bc m rm)
        (MM: mmatch bc m mtop)
        (GE: genv_match bc ge)
        (NOSTK: bc_nostack bc),
      sound_state (Returnstate s v m).

(** Properties of the [sound_stack] invariant on call stacks. *)

Lemma sound_stack_ext:
  forall m' bc stk m bound,
  sound_stack bc stk m bound ->
  (forall b ofs n bytes,
       Plt b bound -> bc b = BCinvalid -> n >= 0 ->
       Mem.loadbytes m' b ofs n = Some bytes ->
       Mem.loadbytes m b ofs n = Some bytes) ->
  sound_stack bc stk m' bound.
Proof.
  induction 1; intros INV.
- constructor.
- assert (Plt sp bound') by eauto with va. 
  eapply sound_stack_public_call; eauto. apply IHsound_stack; intros.
  apply INV. xomega. rewrite SAME; auto. xomega. auto. auto.
- assert (Plt sp bound') by eauto with va. 
  eapply sound_stack_private_call; eauto. apply IHsound_stack; intros.
  apply INV. xomega. rewrite SAME; auto. xomega. auto. auto.
  apply bmatch_ext with m; auto. intros. apply INV. xomega. auto. auto. auto.
Qed.

Lemma sound_stack_inv:
  forall m' bc stk m bound,
  sound_stack bc stk m bound ->
  (forall b ofs n, Plt b bound -> bc b = BCinvalid -> n >= 0 -> Mem.loadbytes m' b ofs n = Mem.loadbytes m b ofs n) ->
  sound_stack bc stk m' bound.
Proof.
  intros. eapply sound_stack_ext; eauto. intros. rewrite <- H0; auto. 
Qed.

Lemma sound_stack_storev:
  forall chunk m addr v m' bc aaddr stk bound,
  Mem.storev chunk m addr v = Some m' ->
  vmatch bc addr aaddr ->
  sound_stack bc stk m bound ->
  sound_stack bc stk m' bound.
Proof.
  intros. apply sound_stack_inv with m; auto. 
  destruct addr; simpl in H; try discriminate.
  assert (A: pmatch bc b i Ptop).
  { inv H0; eapply pmatch_top'; eauto. }
  inv A. 
  intros. eapply Mem.loadbytes_store_other; eauto. left; congruence. 
Qed. 

Lemma sound_stack_storebytes:
  forall m b ofs bytes m' bc aaddr stk bound,
  Mem.storebytes m b (Int.unsigned ofs) bytes = Some m' ->
  vmatch bc (Vptr b ofs) aaddr ->
  sound_stack bc stk m bound ->
  sound_stack bc stk m' bound.
Proof.
  intros. apply sound_stack_inv with m; auto. 
  assert (A: pmatch bc b ofs Ptop).
  { inv H0; eapply pmatch_top'; eauto. }
  inv A. 
  intros. eapply Mem.loadbytes_storebytes_other; eauto. left; congruence. 
Qed. 

Lemma sound_stack_free:
  forall m b lo hi m' bc stk bound,
  Mem.free m b lo hi = Some m' ->
  sound_stack bc stk m bound ->
  sound_stack bc stk m' bound.
Proof.
  intros. eapply sound_stack_ext; eauto. intros.
  eapply Mem.loadbytes_free_2; eauto.
Qed.

Lemma sound_stack_new_bound:
  forall bc stk m bound bound',
  sound_stack bc stk m bound ->
  Ple bound bound' ->
  sound_stack bc stk m bound'.
Proof.
  intros. inv H. 
- constructor.
- eapply sound_stack_public_call with (bound' := bound'0); eauto. xomega. 
- eapply sound_stack_private_call with (bound' := bound'0); eauto. xomega. 
Qed.

Lemma sound_stack_exten:
  forall bc stk m bound (bc1: block_classification),
  sound_stack bc stk m bound ->
  (forall b, Plt b bound -> bc1 b = bc b) ->
  sound_stack bc1 stk m bound.
Proof.
  intros. inv H. 
- constructor.
- assert (Plt sp bound') by eauto with va. 
  eapply sound_stack_public_call; eauto.
  rewrite H0; auto. xomega. 
  intros. rewrite H0; auto. xomega.
- assert (Plt sp bound') by eauto with va. 
  eapply sound_stack_private_call; eauto.
  rewrite H0; auto. xomega. 
  intros. rewrite H0; auto. xomega.
Qed.

(** ** Preservation of the semantic invariant by one step of execution *)

Lemma sound_succ_state:
  forall bc pc ae am instr ae' am'  s f sp pc' e' m',
  (analyze rm f)!!pc = VA.State ae am ->
  f.(fn_code)!pc = Some instr ->
  In pc' (successors_instr instr) ->
  transfer f rm pc ae am = VA.State ae' am' ->
  ematch bc e' ae' ->
  mmatch bc m' am' ->
  romatch bc m' rm ->
  genv_match bc ge ->
  bc sp = BCstack ->
  sound_stack bc s m' sp ->
  sound_state (State s f (Vptr sp Int.zero) pc' e' m').
Proof.
  intros. exploit analyze_succ; eauto. intros (ae'' & am'' & AN & EM & MM).
  econstructor; eauto. 
Qed.

Lemma areg_sound:
  forall bc e ae r, ematch bc e ae -> vmatch bc (e#r) (areg ae r).
Proof.
  intros. apply H. 
Qed.

Lemma aregs_sound:
  forall bc e ae rl, ematch bc e ae -> list_forall2 (vmatch bc) (e##rl) (aregs ae rl).
Proof.
  induction rl; simpl; intros. constructor. constructor; auto. apply areg_sound; auto.
Qed.

Hint Resolve areg_sound aregs_sound: va.

Theorem sound_step:
  forall st t st', RTL.step ge st t st' -> sound_state st -> sound_state st'.
Proof.
  induction 1; intros SOUND; inv SOUND.

- (* nop *)
  eapply sound_succ_state; eauto. simpl; auto. 
  unfold transfer; rewrite H. auto.

- (* op *)
  eapply sound_succ_state; eauto. simpl; auto. 
  unfold transfer; rewrite H. eauto. 
  apply ematch_update; auto. eapply eval_static_operation_sound; eauto with va.

- (* load *)
  eapply sound_succ_state; eauto. simpl; auto. 
  unfold transfer; rewrite H. eauto. 
  apply ematch_update; auto. eapply loadv_sound; eauto with va. 
  eapply eval_static_addressing_sound; eauto with va.

- (* store *)
  exploit eval_static_addressing_sound; eauto with va. intros VMADDR.
  eapply sound_succ_state; eauto. simpl; auto. 
  unfold transfer; rewrite H. eauto. 
  eapply storev_sound; eauto. 
  destruct a; simpl in H1; try discriminate. eapply romatch_store; eauto. 
  eapply sound_stack_storev; eauto. 

- (* call *)
  assert (TR: transfer f rm pc ae am = transfer_call ae am args res).
  { unfold transfer; rewrite H; auto. }
  unfold transfer_call in TR. 
  destruct (pincl (am_nonstack am) Nonstack && 
            forallb (fun r : reg => vpincl (areg ae r) Nonstack) args) eqn:NOLEAK.
+ (* private call *)
  InvBooleans.
  exploit analyze_successor; eauto. simpl; eauto. rewrite TR. intros SUCC. 
  exploit hide_stack; eauto. apply pincl_ge; auto.
  intros (bc' & A & B & C & D & E & F & G).
  apply sound_call_state with bc'; auto.
  * eapply sound_stack_private_call with (bound' := Mem.nextblock m) (bc' := bc); eauto.
    apply Ple_refl.
    eapply mmatch_below; eauto.
    eapply mmatch_stack; eauto. 
  * intros. exploit list_in_map_inv; eauto. intros (r & P & Q). subst v. 
    apply D with (areg ae r). 
    rewrite forallb_forall in H2. apply vpincl_ge. apply H2; auto. auto with va.
+ (* public call *)
  exploit analyze_successor; eauto. simpl; eauto. rewrite TR. intros SUCC. 
  exploit anonymize_stack; eauto. intros (bc' & A & B & C & D & E & F & G).
  apply sound_call_state with bc'; auto.
  * eapply sound_stack_public_call with (bound' := Mem.nextblock m) (bc' := bc); eauto.
    apply Ple_refl.
    eapply mmatch_below; eauto.
  * intros. exploit list_in_map_inv; eauto. intros (r & P & Q). subst v. 
    apply D with (areg ae r). auto with va.

- (* tailcall *)
  exploit anonymize_stack; eauto. intros (bc' & A & B & C & D & E & F & G).
  apply sound_call_state with bc'; auto.
  erewrite Mem.nextblock_free by eauto. 
  apply sound_stack_new_bound with stk.
  apply sound_stack_exten with bc.
  eapply sound_stack_free; eauto.
  intros. apply C. apply Plt_ne; auto.
  apply Plt_Ple. eapply mmatch_below; eauto. congruence. 
  intros. exploit list_in_map_inv; eauto. intros (r & P & Q). subst v. 
  apply D with (areg ae r). auto with va.
  eapply romatch_free; eauto. 
  eapply mmatch_free; eauto. 

- (* builtin *)
  assert (SPVALID: Plt sp0 (Mem.nextblock m)) by (eapply mmatch_below; eauto with va).
  assert (TR: transfer f rm pc ae am = transfer_builtin ae am rm ef args res).
  { unfold transfer; rewrite H; auto. }
  unfold transfer_builtin in TR.
  exploit classify_builtin_sound; eauto. destruct (classify_builtin ef args ae). 
+ (* volatile load *)
  intros (addr & VLOAD & VADDR). inv VLOAD.
  eapply sound_succ_state; eauto. simpl; auto.
  apply ematch_update; auto. 
  inv H2.
  * (* true volatile access *)
    assert (V: vmatch bc v0 (Ifptr Glob)).
    { inv H4; constructor. econstructor. eapply GE; eauto. }
    destruct (va_strict tt). apply vmatch_lub_r. apply vnormalize_sound. auto. 
    apply vnormalize_sound. eapply vmatch_ge; eauto. constructor. constructor.
  * (* normal memory access *)
    exploit loadv_sound; eauto. simpl; eauto. intros V.
    destruct (va_strict tt). 
    apply vmatch_lub_l. auto.
    eapply vnormalize_cast; eauto. eapply vmatch_top; eauto. 
+ (* volatile store *)
  intros (addr & src & VSTORE & VADDR & VSRC). inv VSTORE. inv H7.
  * (* true volatile access *)
    eapply sound_succ_state; eauto. simpl; auto.
    apply ematch_update; auto. constructor.
    apply mmatch_lub_l; auto.
  * (* normal memory access *)
    eapply sound_succ_state; eauto. simpl; auto.
    apply ematch_update; auto. constructor.
    apply mmatch_lub_r. eapply storev_sound; eauto. auto.
    eapply romatch_store; eauto.
    eapply sound_stack_storev; eauto. simpl; eauto.
+ (* memcpy *)
  intros (dst & src & MEMCPY & VDST & VSRC). inv MEMCPY.
  eapply sound_succ_state; eauto. simpl; auto. 
  apply ematch_update; auto. constructor.
  eapply storebytes_sound; eauto. 
  apply match_aptr_of_aval; auto. 
  eapply Mem.loadbytes_length; eauto. 
  intros. eapply loadbytes_sound; eauto. apply match_aptr_of_aval; auto. 
  eapply romatch_storebytes; eauto. 
  eapply sound_stack_storebytes; eauto. 
+ (* annot *)
  intros (A & B); subst. 
  eapply sound_succ_state; eauto. simpl; auto. 
  apply ematch_update; auto. constructor.
+ (* annot val *)
  intros (A & B); subst. 
  eapply sound_succ_state; eauto. simpl; auto. 
  apply ematch_update; auto.
+ (* general case *)
  intros _.
  unfold transfer_call in TR. 
  destruct (pincl (am_nonstack am) Nonstack && 
            forallb (fun r : reg => vpincl (areg ae r) Nonstack) args) eqn:NOLEAK.
* (* private builtin call *)
  InvBooleans. rewrite forallb_forall in H2.
  exploit hide_stack; eauto. apply pincl_ge; auto.
  intros (bc1 & A & B & C & D & E & F & G).
  exploit external_call_match; eauto. 
  intros. exploit list_in_map_inv; eauto. intros (r & P & Q). subst v0. 
  eapply D; eauto with va. apply vpincl_ge. apply H2; auto. 
  intros (bc2 & J & K & L & M & N & O & P & Q).
  exploit (return_from_private_call bc bc2); eauto.
  eapply mmatch_below; eauto.
  rewrite K; auto.
  intros. rewrite K; auto. rewrite C; auto.
  apply bmatch_inv with m. eapply mmatch_stack; eauto. 
  intros. apply Q; auto.
  eapply external_call_nextblock; eauto. 
  intros (bc3 & U & V & W & X & Y & Z & AA).
  eapply sound_succ_state with (bc := bc3); eauto. simpl; auto. 
  apply ematch_update; auto.
  apply sound_stack_exten with bc. 
  apply sound_stack_inv with m. auto.
  intros. apply Q. red. eapply Plt_trans; eauto.
  rewrite C; auto.
  exact AA.
* (* public builtin call *)
  exploit anonymize_stack; eauto. 
  intros (bc1 & A & B & C & D & E & F & G).
  exploit external_call_match; eauto. 
  intros. exploit list_in_map_inv; eauto. intros (r & P & Q). subst v0. eapply D; eauto with va.
  intros (bc2 & J & K & L & M & N & O & P & Q).
  exploit (return_from_public_call bc bc2); eauto.
  eapply mmatch_below; eauto.
  rewrite K; auto.
  intros. rewrite K; auto. rewrite C; auto.
  eapply external_call_nextblock; eauto. 
  intros (bc3 & U & V & W & X & Y & Z & AA).
  eapply sound_succ_state with (bc := bc3); eauto. simpl; auto. 
  apply ematch_update; auto.
  apply sound_stack_exten with bc. 
  apply sound_stack_inv with m. auto.
  intros. apply Q. red. eapply Plt_trans; eauto.
  rewrite C; auto.
  exact AA.

- (* cond *)
  eapply sound_succ_state; eauto. 
  simpl. destruct b; auto. 
  unfold transfer; rewrite H; auto. 

- (* jumptable *)
  eapply sound_succ_state; eauto. 
  simpl. eapply list_nth_z_in; eauto. 
  unfold transfer; rewrite H; auto.

- (* return *)
  exploit anonymize_stack; eauto. intros (bc' & A & B & C & D & E & F & G).
  apply sound_return_state with bc'; auto.
  erewrite Mem.nextblock_free by eauto. 
  apply sound_stack_new_bound with stk.
  apply sound_stack_exten with bc.
  eapply sound_stack_free; eauto.
  intros. apply C. apply Plt_ne; auto.
  apply Plt_Ple. eapply mmatch_below; eauto with va.
  destruct or; simpl. eapply D; eauto. constructor. 
  eapply romatch_free; eauto. 
  eapply mmatch_free; eauto.

- (* internal function *)
  exploit allocate_stack; eauto. 
  intros (bc' & A & B & C & D & E & F & G).
  exploit (analyze_entrypoint rm f args m' bc'); eauto. 
  intros (ae & am & AN & EM & MM').
  econstructor; eauto. 
  erewrite Mem.alloc_result by eauto. 
  apply sound_stack_exten with bc; auto.
  apply sound_stack_inv with m; auto. 
  intros. eapply Mem.loadbytes_alloc_unchanged; eauto.
  intros. apply F. erewrite Mem.alloc_result by eauto. auto.

- (* external function *)
  exploit external_call_match; eauto with va.
  intros (bc' & A & B & C & D & E & F & G & K).
  econstructor; eauto. 
  apply sound_stack_new_bound with (Mem.nextblock m).
  apply sound_stack_exten with bc; auto.
  apply sound_stack_inv with m; auto. 
  eapply external_call_nextblock; eauto.

- (* return *)
  inv STK.
  + (* from public call *)
   exploit return_from_public_call; eauto. 
   intros; rewrite SAME; auto.
   intros (bc1 & A & B & C & D & E & F & G). 
   destruct (analyze rm f)#pc as [ |ae' am'] eqn:EQ; simpl in AN; try contradiction. destruct AN as [A1 A2].
   eapply sound_regular_state with (bc := bc1); eauto.
   apply sound_stack_exten with bc'; auto.
   eapply ematch_ge; eauto. apply ematch_update. auto. auto. 
  + (* from private call *)
   exploit return_from_private_call; eauto. 
   intros; rewrite SAME; auto.
   intros (bc1 & A & B & C & D & E & F & G). 
   destruct (analyze rm f)#pc as [ |ae' am'] eqn:EQ; simpl in AN; try contradiction. destruct AN as [A1 A2].
   eapply sound_regular_state with (bc := bc1); eauto.
   apply sound_stack_exten with bc'; auto.
   eapply ematch_ge; eauto. apply ematch_update. auto. auto.
Qed.

End PAST.

Inductive sound_state_ext (st:state): Prop :=
| sound_state_ext_intro
    (Hsound:
       forall prm (Hprm: PTree_le prm (romem_for_program prog)),
       sound_state prm st)
.

Theorem sound_past_step:
  forall st t st', RTL.step ge st t st' -> sound_state_ext st -> sound_state_ext st'.
Proof.
  intros. inv H0. constructor. intros.
  specialize (Hsound prm Hprm). eapply sound_step; eauto.
Qed.

Theorem sound_past_star:
  forall st t st', Smallstep.star RTL.step ge st t st' -> sound_state_ext st -> sound_state_ext st'.
Proof.
  intros st t st' H. induction H; subst; auto.
  intro X. apply IHstar. eapply sound_past_step; eauto.
Qed.

Theorem sound_past_plus:
  forall st t st', Smallstep.plus RTL.step ge st t st' -> sound_state_ext st -> sound_state_ext st'.
Proof.
  intros st t st' H. destruct H. subst.
  intro X. eapply sound_past_star; eauto.
  eapply sound_past_step; eauto.
Qed.

End SOUNDNESS.

(** ** Soundness of the initial memory abstraction *)

Require Import Axioms.

Theorem sound_initial:
  forall prog st, initial_state prog st -> sound_state_ext prog st.
Proof.
  destruct 1. 
  exploit initial_mem_matches; eauto. intros (bc & GE & BELOW & NOSTACK & RM & VALID).
  constructor. intros.
  apply sound_call_state with bc. 
- constructor. 
- simpl; tauto. 
- repeat intro. inv Hprm. exploit H5; eauto.
- apply mmatch_inj_top with m0.
  replace (inj_of_bc bc) with (Mem.flat_inj (Mem.nextblock m0)).
  eapply Genv.initmem_inject; eauto.
  symmetry; apply extensionality; unfold Mem.flat_inj; intros x.
  destruct (plt x (Mem.nextblock m0)). 
  apply inj_of_bc_valid; auto. 
  unfold inj_of_bc. erewrite bc_below_invalid; eauto.
- exact GE.
- exact NOSTACK.
Qed.

Hint Resolve areg_sound aregs_sound: va.

(** * Interface with other optimizations *)

Lemma avalue_sound:
  forall prog s f sp pc e m r
         prm (Hprm: PTree_le prm (romem_for_program prog)),
  sound_state_ext prog (State s f (Vptr sp Int.zero) pc e m) ->
  exists bc,
     vmatch bc e#r (avalue (analyze prm f)!!pc r)
  /\ genv_match bc (Genv.globalenv prog)
  /\ bc sp = BCstack.
Proof.
  intros. inv H. specialize (Hsound prm Hprm). inv Hsound. exists bc; split; auto. rewrite AN. apply EM.
Qed. 

Lemma aaddr_sound:
  forall prog s f sp pc e m r b ofs
         prm (Hprm: PTree_le prm (romem_for_program prog)),
  sound_state_ext prog (State s f (Vptr sp Int.zero) pc e m) ->
  e#r = Vptr b ofs ->
  exists bc,
     pmatch bc b ofs (aaddr (analyze prm f)!!pc r)
  /\ genv_match bc (Genv.globalenv prog)
  /\ bc sp = BCstack.
Proof.
  intros. inv H. specialize (Hsound prm Hprm). inv Hsound. exists bc; split; auto.
  unfold aaddr; rewrite AN. apply match_aptr_of_aval. rewrite <- H0. apply EM.
Qed. 

Lemma aaddressing_sound:
  forall prog s f sp pc e m addr args b ofs
         prm (Hprm: PTree_le prm (romem_for_program prog)),
  sound_state_ext prog (State s f (Vptr sp Int.zero) pc e m) ->
  eval_addressing (Genv.globalenv prog) (Vptr sp Int.zero) addr e##args = Some (Vptr b ofs) ->
  exists bc,
     pmatch bc b ofs (aaddressing (analyze prm f)!!pc addr args)
  /\ genv_match bc (Genv.globalenv prog)
  /\ bc sp = BCstack.
Proof.
  intros. inv H. specialize (Hsound prm Hprm). inv Hsound. exists bc; split; auto. 
  unfold aaddressing. rewrite AN. apply match_aptr_of_aval. 
  eapply eval_static_addressing_sound; eauto with va.
Qed.
