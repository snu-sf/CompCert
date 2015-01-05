Require Import RelationClasses.
Require Import Classical.
Require Import Coqlib Coqlib_linker.
Require Import Errors.
Require Import Maps Maps_linker.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Events.
Require Import Smallstep.
Require Import Language Linker Linkeq.
Require Import ProgramLSim FunctionLSim.
Require Import Op.
Require Import Registers.
Require Import Inlining.
Require Import Inliningspec.
Require Import RTL.
Require Import Inliningproof.
Require Import RTL_linker ValueAnalysis_linker.
Require Import WFType paco.

Set Implicit Arguments.

(** A (compile-time) function environment is compatible with a
  (run-time) global environment if the following condition holds. *)

Lemma funenv_program_spec p i:
  (funenv_program p) ! i =
  match find (fun id => peq i (fst id)) (rev p.(prog_defs)) with
    | Some (_, Gfun (Internal f)) =>
      if should_inline i f then Some f else None
    | _ => None
  end.
Proof.
  unfold funenv_program. rewrite <- fold_left_rev_right.
  induction (rev (prog_defs p)); simpl.
  { apply PTree.gempty. }
  destruct a. simpl. destruct g; simpl.
  - destruct f; simpl.
    + destruct (should_inline i0 f) eqn:Hinline.
      * rewrite PTree.gsspec. destruct (peq i i0); subst; simpl; auto.
        rewrite Hinline. auto.
      * rewrite PTree.grspec. unfold PTree.elt_eq.
        destruct (peq i i0); subst; simpl; auto.
        rewrite Hinline. auto.
    + rewrite PTree.grspec. unfold PTree.elt_eq.
      destruct (peq i i0); subst; simpl; auto.
  - rewrite PTree.grspec. unfold PTree.elt_eq.
    destruct (peq i i0); simpl; auto.
Qed.

Lemma program_linkeq_fenv_le prog fprog
      (Hlink: program_linkeq Language_RTL prog fprog):
  PTree_le (funenv_program prog) (funenv_program fprog).
Proof.
  constructor. intros. rewrite ? funenv_program_spec in *.
  match goal with
    | [H: context[find ?f ?l] |- _] => destruct (find f l) as [[]|] eqn:Hf; inv H
  end.
  destruct g; inv H0. destruct f; inv H1. destruct (should_inline b f) eqn:Hinline; inv H0.
  destruct Hlink as [Hdefs Hmain]. exploit Hdefs; eauto.
  { rewrite PTree_guespec. instantiate (2 := b).
    unfold fundef, ident in *. simpl in *. rewrite Hf. simpl. eauto.
  }
  intros [def2 [Hdef2 Hle]]. inv Hle. inv Hv.
  - rewrite PTree_guespec in Hdef2. unfold fundef, ident. simpl in *.
    match goal with
      | [|- context[find ?f ?l]] => destruct (find f l) as [[]|] eqn:Hf'; inv Hdef2
    end.
    rewrite Hinline. auto.
  - inv H; simpl in *; inv H1.
Qed.

Section INLINING.

Variable (prog tprog: program).
Hypothesis TRANSF: transf_program prog = OK tprog.

Section FUTURE.

Variable (fprog ftprog:program).
Hypothesis (Hfsim: @program_weak_lsim Language_RTL Language_RTL transf_sigT transf_efT transf_vT
                                      fprog ftprog).

Hypothesis (Hfprog: program_linkeq Language_RTL prog fprog).
Hypothesis (Hftprog: program_linkeq Language_RTL tprog ftprog).

Let globfun_weak_lsim :=
  @globfun_lsim Language_RTL Language_RTL id (@Errors.OK _)
                (fun _ _ _ _ => True)
                fprog ftprog.

Let ge := Genv.globalenv fprog.
Let tge := Genv.globalenv ftprog.

(** ** Relating global environments *)

Inductive match_globalenvs (F: meminj) (bound: block): Prop :=
  | mk_match_globalenvs
      (DOMAIN: forall b, Plt b bound -> F b = Some(b, 0))
      (IMAGE: forall b1 b2 delta, F b1 = Some(b2, delta) -> Plt b2 bound -> b1 = b2)
      (SYMBOLS: forall id b, Genv.find_symbol ge id = Some b -> Plt b bound)
      (FUNCTIONS: forall b fd, Genv.find_funct_ptr ge b = Some fd -> Plt b bound)
      (VARINFOS: forall b gv, Genv.find_var_info ge b = Some gv -> Plt b bound).

Lemma find_function_agree:
  forall ros rs fd F ctx rs' bound,
  find_function ge ros rs = Some fd ->
  agree_regs F ctx rs rs' ->
  match_globalenvs F bound ->
  exists fd',
  find_function tge (sros ctx ros) rs' = Some fd' /\
  fundef_weak_lsim Language_RTL Language_RTL id ge tge fd fd'.
Proof.
  intros. destruct ros as [r | id]; simpl in *.
  (* register *)
  assert (rs'#(sreg ctx r) = rs#r).
    exploit Genv.find_funct_inv; eauto. intros [b EQ].
    assert (A: val_inject F rs#r rs'#(sreg ctx r)). eapply agree_val_reg; eauto.
    rewrite EQ in A; inv A.
    inv H1. rewrite DOMAIN in H5. inv H5. auto.
    apply FUNCTIONS with fd. 
    rewrite EQ in H; rewrite Genv.find_funct_find_funct_ptr in H. auto.
  rewrite H2. eapply functions_translated; eauto.
  (* symbol *)
  unfold ge, tge in *. erewrite symbols_preserved; try apply Hfsim. destruct (Genv.find_symbol (Genv.globalenv fprog) id); try discriminate.
  eapply funct_ptr_translated; eauto.
Qed.

(** ** Relating stacks *)

Inductive match_stacks (F: meminj) (m m': mem):
             list stackframe -> list stackframe -> block -> Prop :=
  | match_stacks_nil: forall bound1 bound
        (MG: match_globalenvs F bound1)
        (BELOW: Ple bound1 bound),
      match_stacks F m m' nil nil bound
  | match_stacks_cons: forall res f sp pc rs stk f' sp' rs' stk' bound ctx fenv
        (MS: match_stacks_inside F m m' stk stk' f' ctx sp' rs')
        (FENV: PTree_le fenv (funenv_program fprog))
        (FB: tr_funbody fenv f'.(fn_stacksize) ctx f f'.(fn_code))
        (AG: agree_regs F ctx rs rs')
        (SP: F sp = Some(sp', ctx.(dstk)))
        (PRIV: range_private F m m' sp' (ctx.(dstk) + ctx.(mstk)) f'.(fn_stacksize))
        (SSZ1: 0 <= f'.(fn_stacksize) < Int.max_unsigned)
        (SSZ2: forall ofs, Mem.perm m' sp' ofs Max Nonempty -> 0 <= ofs <= f'.(fn_stacksize))
        (RES: Ple res ctx.(mreg))
        (BELOW: Plt sp' bound),
      match_stacks F m m'
                   (Stackframe res f (Vptr sp Int.zero) pc rs :: stk)
                   (Stackframe (sreg ctx res) f' (Vptr sp' Int.zero) (spc ctx pc) rs' :: stk')
                   bound
  | match_stacks_untailcall: forall stk res f' sp' rpc rs' stk' bound ctx
        (MS: match_stacks_inside F m m' stk stk' f' ctx sp' rs')
        (PRIV: range_private F m m' sp' ctx.(dstk) f'.(fn_stacksize))
        (SSZ1: 0 <= f'.(fn_stacksize) < Int.max_unsigned)
        (SSZ2: forall ofs, Mem.perm m' sp' ofs Max Nonempty -> 0 <= ofs <= f'.(fn_stacksize))
        (RET: ctx.(retinfo) = Some (rpc, res))
        (BELOW: Plt sp' bound),
      match_stacks F m m'
                   stk
                   (Stackframe res f' (Vptr sp' Int.zero) rpc rs' :: stk')
                   bound

with match_stacks_inside (F: meminj) (m m': mem):
        list stackframe -> list stackframe -> function -> context -> block -> regset -> Prop :=
  | match_stacks_inside_base: forall stk stk' f' ctx sp' rs'
        (MS: match_stacks F m m' stk stk' sp')
        (RET: ctx.(retinfo) = None)
        (DSTK: ctx.(dstk) = 0),
      match_stacks_inside F m m' stk stk' f' ctx sp' rs'
  | match_stacks_inside_inlined: forall res f sp pc rs stk stk' f' ctx sp' rs' ctx' fenv
        (MS: match_stacks_inside F m m' stk stk' f' ctx' sp' rs')
        (FENV: PTree_le fenv (funenv_program fprog))
        (FB: tr_funbody fenv f'.(fn_stacksize) ctx' f f'.(fn_code))
        (AG: agree_regs F ctx' rs rs')
        (SP: F sp = Some(sp', ctx'.(dstk)))
        (PAD: range_private F m m' sp' (ctx'.(dstk) + ctx'.(mstk)) ctx.(dstk))
        (RES: Ple res ctx'.(mreg))
        (RET: ctx.(retinfo) = Some (spc ctx' pc, sreg ctx' res))
        (BELOW: context_below ctx' ctx)
        (SBELOW: context_stack_call ctx' ctx),
      match_stacks_inside F m m' (Stackframe res f (Vptr sp Int.zero) pc rs :: stk)
                                 stk' f' ctx sp' rs'.

(** Properties of match_stacks *)

Section MATCH_STACKS.

Variable F: meminj.
Variables m m': mem.

Lemma match_stacks_globalenvs:
  forall stk stk' bound,
  match_stacks F m m' stk stk' bound -> exists b, match_globalenvs F b
with match_stacks_inside_globalenvs:
  forall stk stk' f ctx sp rs', 
  match_stacks_inside F m m' stk stk' f ctx sp rs' -> exists b, match_globalenvs F b.
Proof.
  induction 1; eauto.
  induction 1; eauto.
Qed.

Lemma match_globalenvs_preserves_globals:
  forall b, match_globalenvs F b -> meminj_preserves_globals ge F.
Proof.
  intros. inv H. red. split. eauto. split. eauto.
  intros. symmetry. eapply IMAGE; eauto.
Qed. 

Lemma match_stacks_inside_globals:
  forall stk stk' f ctx sp rs', 
  match_stacks_inside F m m' stk stk' f ctx sp rs' -> meminj_preserves_globals ge F.
Proof.
  intros. exploit match_stacks_inside_globalenvs; eauto. intros [b A]. 
  eapply match_globalenvs_preserves_globals; eauto.
Qed.

Lemma match_stacks_bound:
  forall stk stk' bound bound1,
  match_stacks F m m' stk stk' bound ->
  Ple bound bound1 ->
  match_stacks F m m' stk stk' bound1.
Proof.
  intros. inv H.
  apply match_stacks_nil with bound0. auto. eapply Ple_trans; eauto. 
  eapply match_stacks_cons; eauto. eapply Plt_le_trans; eauto. 
  eapply match_stacks_untailcall; eauto. eapply Plt_le_trans; eauto. 
Qed. 

Variable F1: meminj.
Variables m1 m1': mem.
Hypothesis INCR: inject_incr F F1.

Lemma match_stacks_invariant:
  forall stk stk' bound, match_stacks F m m' stk stk' bound ->
  forall (INJ: forall b1 b2 delta, 
               F1 b1 = Some(b2, delta) -> Plt b2 bound -> F b1 = Some(b2, delta))
         (PERM1: forall b1 b2 delta ofs,
               F1 b1 = Some(b2, delta) -> Plt b2 bound ->
               Mem.perm m1 b1 ofs Max Nonempty -> Mem.perm m b1 ofs Max Nonempty)
         (PERM2: forall b ofs, Plt b bound ->
               Mem.perm m' b ofs Cur Freeable -> Mem.perm m1' b ofs Cur Freeable)
         (PERM3: forall b ofs k p, Plt b bound ->
               Mem.perm m1' b ofs k p -> Mem.perm m' b ofs k p),
  match_stacks F1 m1 m1' stk stk' bound

with match_stacks_inside_invariant:
  forall stk stk' f' ctx sp' rs1, 
  match_stacks_inside F m m' stk stk' f' ctx sp' rs1 ->
  forall rs2
         (RS: forall r, Plt r ctx.(dreg) -> rs2#r = rs1#r)
         (INJ: forall b1 b2 delta, 
               F1 b1 = Some(b2, delta) -> Ple b2 sp' -> F b1 = Some(b2, delta))
         (PERM1: forall b1 b2 delta ofs,
               F1 b1 = Some(b2, delta) -> Ple b2 sp' ->
               Mem.perm m1 b1 ofs Max Nonempty -> Mem.perm m b1 ofs Max Nonempty)
         (PERM2: forall b ofs, Ple b sp' ->
               Mem.perm m' b ofs Cur Freeable -> Mem.perm m1' b ofs Cur Freeable)
         (PERM3: forall b ofs k p, Ple b sp' ->
               Mem.perm m1' b ofs k p -> Mem.perm m' b ofs k p),
  match_stacks_inside F1 m1 m1' stk stk' f' ctx sp' rs2.

Proof.
  induction 1; intros.
  (* nil *)
  apply match_stacks_nil with (bound1 := bound1).
  inv MG. constructor; auto. 
  intros. apply IMAGE with delta. eapply INJ; eauto. eapply Plt_le_trans; eauto.
  auto. auto.
  (* cons *)
  apply match_stacks_cons with (ctx := ctx) (fenv := fenv); auto.
  eapply match_stacks_inside_invariant; eauto.
  intros; eapply INJ; eauto; xomega. 
  intros; eapply PERM1; eauto; xomega.
  intros; eapply PERM2; eauto; xomega.
  intros; eapply PERM3; eauto; xomega.
  eapply agree_regs_incr; eauto.
  eapply range_private_invariant; eauto. 
  (* untailcall *)
  apply match_stacks_untailcall with (ctx := ctx); auto. 
  eapply match_stacks_inside_invariant; eauto.
  intros; eapply INJ; eauto; xomega.
  intros; eapply PERM1; eauto; xomega.
  intros; eapply PERM2; eauto; xomega.
  intros; eapply PERM3; eauto; xomega.
  eapply range_private_invariant; eauto. 

  induction 1; intros.
  (* base *)
  eapply match_stacks_inside_base; eauto.
  eapply match_stacks_invariant; eauto. 
  intros; eapply INJ; eauto; xomega.
  intros; eapply PERM1; eauto; xomega.
  intros; eapply PERM2; eauto; xomega.
  intros; eapply PERM3; eauto; xomega.
  (* inlined *)
  apply match_stacks_inside_inlined with (ctx' := ctx') (fenv := fenv); auto. 
  apply IHmatch_stacks_inside; auto.
  intros. apply RS. red in BELOW. xomega. 
  apply agree_regs_incr with F; auto. 
  apply agree_regs_invariant with rs'; auto. 
  intros. apply RS. red in BELOW. xomega. 
  eapply range_private_invariant; eauto.
    intros. split. eapply INJ; eauto. xomega. eapply PERM1; eauto. xomega.
    intros. eapply PERM2; eauto. xomega.
Qed.

Lemma match_stacks_empty:
  forall stk stk' bound,
  match_stacks F m m' stk stk' bound -> stk = nil -> stk' = nil
with match_stacks_inside_empty:
  forall stk stk' f ctx sp rs,
  match_stacks_inside F m m' stk stk' f ctx sp rs -> stk = nil -> stk' = nil /\ ctx.(retinfo) = None.
Proof.
  induction 1; intros.
  auto.
  discriminate.
  exploit match_stacks_inside_empty; eauto. intros [A B]. congruence.
  induction 1; intros.
  split. eapply match_stacks_empty; eauto. auto.
  discriminate.
Qed.

End MATCH_STACKS.

(** Preservation by assignment to a register *)

Lemma match_stacks_inside_set_reg:
  forall F m m' stk stk' f' ctx sp' rs' r v, 
  match_stacks_inside F m m' stk stk' f' ctx sp' rs' ->
  match_stacks_inside F m m' stk stk' f' ctx sp' (rs'#(sreg ctx r) <- v).
Proof.
  intros. eapply match_stacks_inside_invariant; eauto. 
  intros. apply Regmap.gso. zify. unfold sreg; rewrite shiftpos_eq. xomega.
Qed.

(** Preservation by a memory store *)

Lemma match_stacks_inside_store:
  forall F m m' stk stk' f' ctx sp' rs' chunk b ofs v m1 chunk' b' ofs' v' m1', 
  match_stacks_inside F m m' stk stk' f' ctx sp' rs' ->
  Mem.store chunk m b ofs v = Some m1 ->
  Mem.store chunk' m' b' ofs' v' = Some m1' ->
  match_stacks_inside F m1 m1' stk stk' f' ctx sp' rs'.
Proof.
  intros. 
  eapply match_stacks_inside_invariant; eauto with mem.
Qed.

(** Preservation by an allocation *)

Lemma match_stacks_inside_alloc_left:
  forall F m m' stk stk' f' ctx sp' rs',
  match_stacks_inside F m m' stk stk' f' ctx sp' rs' ->
  forall sz m1 b F1 delta,
  Mem.alloc m 0 sz = (m1, b) ->
  inject_incr F F1 ->
  F1 b = Some(sp', delta) ->
  (forall b1, b1 <> b -> F1 b1 = F b1) ->
  delta >= ctx.(dstk) ->
  match_stacks_inside F1 m1 m' stk stk' f' ctx sp' rs'.
Proof.
  induction 1; intros.
  (* base *)
  eapply match_stacks_inside_base; eauto. 
  eapply match_stacks_invariant; eauto.
  intros. destruct (eq_block b1 b).
  subst b1. rewrite H1 in H4; inv H4. eelim Plt_strict; eauto. 
  rewrite H2 in H4; auto. 
  intros. exploit Mem.perm_alloc_inv; eauto. destruct (eq_block b1 b); intros; auto.
  subst b1. rewrite H1 in H4. inv H4. eelim Plt_strict; eauto. 
  (* inlined *)
  eapply match_stacks_inside_inlined; eauto. 
  eapply IHmatch_stacks_inside; eauto. destruct SBELOW. omega. 
  eapply agree_regs_incr; eauto.
  eapply range_private_invariant; eauto. 
  intros. exploit Mem.perm_alloc_inv; eauto. destruct (eq_block b0 b); intros.
  subst b0. rewrite H2 in H5; inv H5. elimtype False; xomega. 
  rewrite H3 in H5; auto. 
Qed.

(** Preservation by freeing *)

Lemma match_stacks_free_left:
  forall F m m' stk stk' sp b lo hi m1,
  match_stacks F m m' stk stk' sp ->
  Mem.free m b lo hi = Some m1 ->
  match_stacks F m1 m' stk stk' sp.
Proof.
  intros. eapply match_stacks_invariant; eauto.
  intros. eapply Mem.perm_free_3; eauto. 
Qed.

Lemma match_stacks_free_right:
  forall F m m' stk stk' sp lo hi m1',
  match_stacks F m m' stk stk' sp ->
  Mem.free m' sp lo hi = Some m1' ->
  match_stacks F m m1' stk stk' sp.
Proof.
  intros. eapply match_stacks_invariant; eauto. 
  intros. eapply Mem.perm_free_1; eauto. 
  intros. eapply Mem.perm_free_3; eauto.
Qed.

Lemma min_alignment_sound:
  forall sz n, (min_alignment sz | n) -> Mem.inj_offset_aligned n sz.
Proof.
  intros; red; intros. unfold min_alignment in H. 
  assert (2 <= sz -> (2 | n)). intros.
    destruct (zle sz 1). omegaContradiction.
    destruct (zle sz 2). auto. 
    destruct (zle sz 4). apply Zdivides_trans with 4; auto. exists 2; auto.
    apply Zdivides_trans with 8; auto. exists 4; auto.
  assert (4 <= sz -> (4 | n)). intros.
    destruct (zle sz 1). omegaContradiction.
    destruct (zle sz 2). omegaContradiction.
    destruct (zle sz 4). auto.
    apply Zdivides_trans with 8; auto. exists 2; auto.
  assert (8 <= sz -> (8 | n)). intros.
    destruct (zle sz 1). omegaContradiction.
    destruct (zle sz 2). omegaContradiction.
    destruct (zle sz 4). omegaContradiction.
    auto.
  destruct chunk; simpl in *; auto.
  apply Zone_divide.
  apply Zone_divide.
  apply H2; omega.
  apply H2; omega.
Qed.

(** Preservation by external calls *)

Section EXTCALL.

Variables F1 F2: meminj.
Variables m1 m2 m1' m2': mem.
Hypothesis MAXPERM: forall b ofs p, Mem.valid_block m1 b -> Mem.perm m2 b ofs Max p -> Mem.perm m1 b ofs Max p.
Hypothesis MAXPERM': forall b ofs p, Mem.valid_block m1' b -> Mem.perm m2' b ofs Max p -> Mem.perm m1' b ofs Max p.
Hypothesis UNCHANGED: Mem.unchanged_on (loc_out_of_reach F1 m1) m1' m2'.
Hypothesis INJ: Mem.inject F1 m1 m1'.
Hypothesis INCR: inject_incr F1 F2.
Hypothesis SEP: inject_separated F1 F2 m1 m1'.

Lemma match_stacks_extcall:
  forall stk stk' bound, 
  match_stacks F1 m1 m1' stk stk' bound ->
  Ple bound (Mem.nextblock m1') ->
  match_stacks F2 m2 m2' stk stk' bound
with match_stacks_inside_extcall:
  forall stk stk' f' ctx sp' rs',
  match_stacks_inside F1 m1 m1' stk stk' f' ctx sp' rs' ->
  Plt sp' (Mem.nextblock m1') ->
  match_stacks_inside F2 m2 m2' stk stk' f' ctx sp' rs'.
Proof.
  induction 1; intros.
  apply match_stacks_nil with bound1; auto. 
    inv MG. constructor; intros; eauto. 
    destruct (F1 b1) as [[b2' delta']|] eqn:?.
    exploit INCR; eauto. intros EQ; rewrite H0 in EQ; inv EQ. eapply IMAGE; eauto. 
    exploit SEP; eauto. intros [A B]. elim B. red. xomega. 
  eapply match_stacks_cons; eauto. 
    eapply match_stacks_inside_extcall; eauto. xomega. 
    eapply agree_regs_incr; eauto. 
    eapply range_private_extcall; eauto. red; xomega. 
    intros. apply SSZ2; auto. apply MAXPERM'; auto. red; xomega.
  eapply match_stacks_untailcall; eauto. 
    eapply match_stacks_inside_extcall; eauto. xomega. 
    eapply range_private_extcall; eauto. red; xomega. 
    intros. apply SSZ2; auto. apply MAXPERM'; auto. red; xomega.
  induction 1; intros.
  eapply match_stacks_inside_base; eauto.
    eapply match_stacks_extcall; eauto. xomega. 
  eapply match_stacks_inside_inlined; eauto. 
    eapply agree_regs_incr; eauto. 
    eapply range_private_extcall; eauto.
Qed.

End EXTCALL.

(** Change of context corresponding to an inlined tailcall *)

Lemma align_unchanged:
  forall n amount, amount > 0 -> (amount | n) -> align n amount = n.
Proof.
  intros. destruct H0 as [p EQ]. subst n. unfold align. decEq. 
  apply Zdiv_unique with (b := amount - 1). omega. omega.
Qed.

Lemma match_stacks_inside_inlined_tailcall:
  forall F m m' stk stk' f' ctx sp' rs' ctx' f fenv,
  match_stacks_inside F m m' stk stk' f' ctx sp' rs' ->
  context_below ctx ctx' ->
  context_stack_tailcall ctx f ctx' ->
  ctx'.(retinfo) = ctx.(retinfo) ->
  range_private F m m' sp' ctx.(dstk) f'.(fn_stacksize) ->
  tr_funbody fenv f'.(fn_stacksize) ctx' f f'.(fn_code) ->
  match_stacks_inside F m m' stk stk' f' ctx' sp' rs'.
Proof.
  intros. inv H.
  (* base *)
  eapply match_stacks_inside_base; eauto. congruence. 
  rewrite H1. rewrite DSTK. apply align_unchanged. apply min_alignment_pos. apply Zdivide_0.
  (* inlined *)
  assert (dstk ctx <= dstk ctx'). rewrite H1. apply align_le. apply min_alignment_pos.
  eapply match_stacks_inside_inlined; eauto. 
  red; intros. destruct (zlt ofs (dstk ctx)). apply PAD; omega. apply H3. inv H4. xomega. 
  congruence. 
  unfold context_below in *. xomega.
  unfold context_stack_call in *. omega. 
Qed.

(** ** Relating states *)

Inductive match_states (F:meminj): state -> state -> Prop :=
  | match_regular_states: forall stk f sp pc rs m stk' f' sp' rs' m' ctx fenv
        (MS: match_stacks_inside F m m' stk stk' f' ctx sp' rs')
        (FENV: PTree_le fenv (funenv_program fprog))
        (FB: tr_funbody fenv f'.(fn_stacksize) ctx f f'.(fn_code))
        (AG: agree_regs F ctx rs rs')
        (SP: F sp = Some(sp', ctx.(dstk)))
        (MINJ: Mem.inject F m m')
        (VB: Mem.valid_block m' sp')
        (PRIV: range_private F m m' sp' (ctx.(dstk) + ctx.(mstk)) f'.(fn_stacksize))
        (SSZ1: 0 <= f'.(fn_stacksize) < Int.max_unsigned)
        (SSZ2: forall ofs, Mem.perm m' sp' ofs Max Nonempty -> 0 <= ofs <= f'.(fn_stacksize)),
      match_states F
                   (State stk f (Vptr sp Int.zero) pc rs m)
                   (State stk' f' (Vptr sp' Int.zero) (spc ctx pc) rs' m')
  | match_call_regular_states: forall stk f vargs m stk' f' sp' rs' m' ctx ctx' pc' pc1' rargs fenv
        (MS: match_stacks_inside F m m' stk stk' f' ctx sp' rs')
        (FENV: PTree_le fenv (funenv_program fprog))
        (FB: tr_funbody fenv f'.(fn_stacksize) ctx f f'.(fn_code))
        (BELOW: context_below ctx' ctx)
        (NOP: f'.(fn_code)!pc' = Some(Inop pc1'))
        (MOVES: tr_moves f'.(fn_code) pc1' (sregs ctx' rargs) (sregs ctx f.(fn_params)) (spc ctx f.(fn_entrypoint)))
        (VINJ: list_forall2 (val_reg_charact F ctx' rs') vargs rargs)
        (MINJ: Mem.inject F m m')
        (VB: Mem.valid_block m' sp')
        (PRIV: range_private F m m' sp' ctx.(dstk) f'.(fn_stacksize))
        (SSZ1: 0 <= f'.(fn_stacksize) < Int.max_unsigned)
        (SSZ2: forall ofs, Mem.perm m' sp' ofs Max Nonempty -> 0 <= ofs <= f'.(fn_stacksize)),
      match_states F
                   (Callstate stk (Internal f) vargs m)
                   (State stk' f' (Vptr sp' Int.zero) pc' rs' m')
  | match_return_states: forall stk v m stk' v' m'
        (MS: match_stacks F m m' stk stk' (Mem.nextblock m'))
        (VINJ: val_inject F v v')
        (MINJ: Mem.inject F m m'),
      match_states F
                   (Returnstate stk v m)
                   (Returnstate stk' v' m')
  | match_return_regular_states: forall stk v m stk' f' sp' rs' m' ctx pc' or rinfo
        (MS: match_stacks_inside F m m' stk stk' f' ctx sp' rs')
        (RET: ctx.(retinfo) = Some rinfo)
        (AT: f'.(fn_code)!pc' = Some(inline_return ctx or rinfo))
        (VINJ: match or with None => v = Vundef | Some r => val_inject F v rs'#(sreg ctx r) end)
        (MINJ: Mem.inject F m m')
        (VB: Mem.valid_block m' sp')
        (PRIV: range_private F m m' sp' ctx.(dstk) f'.(fn_stacksize))
        (SSZ1: 0 <= f'.(fn_stacksize) < Int.max_unsigned)
        (SSZ2: forall ofs, Mem.perm m' sp' ofs Max Nonempty -> 0 <= ofs <= f'.(fn_stacksize)),
      match_states F
                   (Returnstate stk v m)
                   (State stk' f' (Vptr sp' Int.zero) pc' rs' m').

Inductive match_call (F:meminj): state -> state -> Prop :=
  | match_call_states: forall stk fd args m stk' fd' args' m'
        (MS: match_stacks F m m' stk stk' (Mem.nextblock m'))
        (FD: fundef_weak_lsim Language_RTL Language_RTL id ge tge fd fd')
        (VINJ: val_list_inject F args args')
        (MINJ: Mem.inject F m m'),
      match_call F
                 (Callstate stk fd args m)
                 (Callstate stk' fd' args' m')
.

(** ** Forward simulation *)

Definition measure (S: state) : nat :=
  match S with
  | State _ _ _ _ _ _ => 1%nat
  | Callstate _ _ _ _ => 0%nat
  | Returnstate _ _ _ => 0%nat
  end.

Lemma tr_funbody_inv:
  forall sz cts f c pc i fenv,
  tr_funbody fenv sz cts f c -> f.(fn_code)!pc = Some i -> tr_instr fenv sz cts pc i c.
Proof.
  intros. inv H. eauto. 
Qed.

Theorem step_simulation:
  forall F S1 t S2,
  step ge S1 t S2 ->
  forall S1' (MS: match_states F S1 S1'),
  (exists F' S2', plus step tge S1' t S2' /\ (match_states F' S2 S2' \/ match_call F' S2 S2'))
  \/ (exists F', measure S2 < measure S1 /\ t = E0 /\ (match_states F' S2 S1' \/ match_call F' S2 S1'))%nat.
Proof.
  induction 1; intros; inv MS.

(* nop *)
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
  left; econstructor; econstructor; split. 
  eapply plus_one. eapply exec_Inop; eauto.
  left. econstructor; eauto.

(* op *)
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
  exploit eval_operation_inject. 
    eapply match_stacks_inside_globals; eauto.
    eexact SP.
    instantiate (2 := rs##args). instantiate (1 := rs'##(sregs ctx args)). eapply agree_val_regs; eauto.
    eexact MINJ. eauto.
  fold (sop ctx op). intros [v' [A B]].
  left; econstructor; econstructor; split.
  eapply plus_one. eapply exec_Iop; eauto. erewrite eval_operation_preserved; eauto.
  apply symbols_preserved. auto.
  left. econstructor; eauto. 
  apply match_stacks_inside_set_reg; auto.
  apply agree_set_reg; auto. 
  
(* load *)
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
  exploit eval_addressing_inject. 
    eapply match_stacks_inside_globals; eauto.
    eexact SP.
    instantiate (2 := rs##args). instantiate (1 := rs'##(sregs ctx args)). eapply agree_val_regs; eauto.
    eauto.
  fold (saddr ctx addr). intros [a' [P Q]].
  exploit Mem.loadv_inject; eauto. intros [v' [U V]].
  assert (eval_addressing tge (Vptr sp' Int.zero) (saddr ctx addr) rs' ## (sregs ctx args) = Some a').
  rewrite <- P. apply eval_addressing_preserved. apply symbols_preserved. auto.
  left; econstructor; econstructor; split.
  eapply plus_one. eapply exec_Iload; eauto.
  left. econstructor; eauto. 
  apply match_stacks_inside_set_reg; auto.
  apply agree_set_reg; auto. 

(* store *)
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
  exploit eval_addressing_inject. 
    eapply match_stacks_inside_globals; eauto.
    eexact SP.
    instantiate (2 := rs##args). instantiate (1 := rs'##(sregs ctx args)). eapply agree_val_regs; eauto.
    eauto.
  fold saddr. intros [a' [P Q]].
  exploit Mem.storev_mapped_inject; eauto. eapply agree_val_reg; eauto. 
  intros [m1' [U V]].
  assert (eval_addressing tge (Vptr sp' Int.zero) (saddr ctx addr) rs' ## (sregs ctx args) = Some a').
    rewrite <- P. apply eval_addressing_preserved. apply symbols_preserved. auto.
  left; econstructor; econstructor; split.
  eapply plus_one. eapply exec_Istore; eauto.
  destruct a; simpl in H1; try discriminate.
  destruct a'; simpl in U; try discriminate.
  left. econstructor; eauto.
  eapply match_stacks_inside_store; eauto.
  eapply Mem.store_valid_block_1; eauto.
  eapply range_private_invariant; eauto.
  intros; split; auto. eapply Mem.perm_store_2; eauto.
  intros; eapply Mem.perm_store_1; eauto.
  intros. eapply SSZ2. eapply Mem.perm_store_2; eauto.

(* call *)
  exploit match_stacks_inside_globalenvs; eauto. intros [bound G].
  exploit find_function_agree; eauto. intros [fd' [A B]].
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
(* not inlined *)
  left; econstructor; econstructor; split.
  eapply plus_one. eapply exec_Icall; eauto.
  eapply sig_preserved; eauto.
  right. econstructor; eauto.
  eapply match_stacks_cons; eauto. 
  eapply agree_val_regs; eauto. 
(* inlined *)
  assert (fd = Internal f0).
    simpl in H0. destruct (Genv.find_symbol ge id) as [b|] eqn:?; try discriminate.
    exploit funenv_program_compat; eauto. apply FENV. eauto. intros.
    unfold ge in H0. congruence.
  subst fd.
  right; econstructor; split. simpl; omega. split. auto. 
  left. econstructor; eauto. 
  eapply match_stacks_inside_inlined; eauto.
  red; intros. apply PRIV. inv H13. destruct H16. xomega.
  apply agree_val_regs_gen; auto.
  red; intros; apply PRIV. destruct H16. omega. 

(* tailcall *)
  exploit match_stacks_inside_globalenvs; eauto. intros [bound G].
  exploit find_function_agree; eauto. intros [fd' [A B]].
  assert (PRIV': range_private F m' m'0 sp' (dstk ctx) f'.(fn_stacksize)).
    eapply range_private_free_left; eauto. inv FB. rewrite <- H4. auto. 
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
(* within the original function *)
  inv MS0; try congruence.
  assert (X: { m1' | Mem.free m'0 sp' 0 (fn_stacksize f') = Some m1'}).
    apply Mem.range_perm_free. red; intros.
    destruct (zlt ofs f.(fn_stacksize)). 
    replace ofs with (ofs + dstk ctx) by omega. eapply Mem.perm_inject; eauto.
    eapply Mem.free_range_perm; eauto. omega.
    inv FB. eapply range_private_perms; eauto. xomega.
  destruct X as [m1' FREE].
  left; econstructor; econstructor; split.
  eapply plus_one. eapply exec_Itailcall; eauto.
  eapply sig_preserved; eauto.
  right. econstructor; eauto.
  eapply match_stacks_bound with (bound := sp'). 
  eapply match_stacks_invariant; eauto.
    intros. eapply Mem.perm_free_3; eauto. 
    intros. eapply Mem.perm_free_1; eauto. 
    intros. eapply Mem.perm_free_3; eauto.
  erewrite Mem.nextblock_free; eauto. red in VB; xomega.
  eapply agree_val_regs; eauto.
  eapply Mem.free_right_inject; eauto. eapply Mem.free_left_inject; eauto.
  (* show that no valid location points into the stack block being freed *)
  intros. rewrite DSTK in PRIV'. exploit (PRIV' (ofs + delta)). omega. intros [P Q]. 
  eelim Q; eauto. replace (ofs + delta - delta) with ofs by omega. 
  apply Mem.perm_max with k. apply Mem.perm_implies with p; auto with mem.
(* turned into a call *)
  left; econstructor; econstructor; split.
  eapply plus_one. eapply exec_Icall; eauto.
  eapply sig_preserved; eauto.
  right. econstructor; eauto.
  eapply match_stacks_untailcall; eauto.
  eapply match_stacks_inside_invariant; eauto. 
    intros. eapply Mem.perm_free_3; eauto.
  eapply agree_val_regs; eauto.
  eapply Mem.free_left_inject; eauto.
(* inlined *)
  assert (fd = Internal f0).
    simpl in H0. destruct (Genv.find_symbol ge id) as [b|] eqn:?; try discriminate.
    exploit funenv_program_compat; eauto. apply FENV. eauto. intros.
    unfold ge in H0. congruence.
  subst fd.
  right; econstructor; split. simpl; omega. split. auto. 
  left. econstructor; eauto.
  eapply match_stacks_inside_inlined_tailcall; eauto.
  eapply match_stacks_inside_invariant; eauto.
    intros. eapply Mem.perm_free_3; eauto.
  apply agree_val_regs_gen; auto.
  eapply Mem.free_left_inject; eauto.
  red; intros; apply PRIV'. 
    assert (dstk ctx <= dstk ctx'). red in H14; rewrite H14. apply align_le. apply min_alignment_pos.
    omega.

(* builtin *)
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
  exploit external_call_mem_inject; eauto. 
    eapply match_stacks_inside_globals; eauto.
    instantiate (1 := rs'##(sregs ctx args)). eapply agree_val_regs; eauto. 
  intros [F1 [v1 [m1' [A [B [C [D [E [J K]]]]]]]]].
  left; econstructor; econstructor; split.
  eapply plus_one. eapply exec_Ibuiltin; eauto. 
    eapply external_call_symbols_preserved; eauto. 
    apply symbols_preserved. auto. apply varinfo_preserved. auto.
  left. econstructor.
    eapply match_stacks_inside_set_reg. 
    eapply match_stacks_inside_extcall with (F1 := F) (F2 := F1) (m1 := m) (m1' := m'0); eauto.
    intros; eapply external_call_max_perm; eauto. 
    intros; eapply external_call_max_perm; eauto. 
  auto. eauto. auto.
  eapply agree_set_reg. eapply agree_regs_incr; eauto. auto. auto. 
  apply J; auto.
  auto. 
  eapply external_call_valid_block; eauto. 
  eapply range_private_extcall; eauto. 
    intros; eapply external_call_max_perm; eauto. 
  auto. 
  intros. apply SSZ2. eapply external_call_max_perm; eauto. 

(* cond *)
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
  assert (eval_condition cond rs'##(sregs ctx args) m' = Some b).
    eapply eval_condition_inject; eauto. eapply agree_val_regs; eauto. 
  left; econstructor; econstructor; split.
  eapply plus_one. eapply exec_Icond; eauto. 
  destruct b; left; econstructor; eauto. 

(* jumptable *)
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
  assert (val_inject F rs#arg rs'#(sreg ctx arg)). eapply agree_val_reg; eauto.
  rewrite H0 in H2; inv H2. 
  left; econstructor; econstructor; split.
  eapply plus_one. eapply exec_Ijumptable; eauto.
  rewrite list_nth_z_map. rewrite H1. simpl; reflexivity. 
  left. econstructor; eauto. 

(* return *)
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
  (* not inlined *)
  inv MS0; try congruence.
  assert (X: { m1' | Mem.free m'0 sp' 0 (fn_stacksize f') = Some m1'}).
    apply Mem.range_perm_free. red; intros.
    destruct (zlt ofs f.(fn_stacksize)). 
    replace ofs with (ofs + dstk ctx) by omega. eapply Mem.perm_inject; eauto.
    eapply Mem.free_range_perm; eauto. omega.
    inv FB. eapply range_private_perms; eauto.
    generalize (Zmax_spec (fn_stacksize f) 0). destruct (zlt 0 (fn_stacksize f)); omega.
  destruct X as [m1' FREE].
  left; econstructor; econstructor; split.
  eapply plus_one. eapply exec_Ireturn; eauto. 
  left. econstructor; eauto.
  eapply match_stacks_bound with (bound := sp'). 
  eapply match_stacks_invariant; eauto.
    intros. eapply Mem.perm_free_3; eauto. 
    intros. eapply Mem.perm_free_1; eauto. 
    intros. eapply Mem.perm_free_3; eauto.
  erewrite Mem.nextblock_free; eauto. red in VB; xomega.
  destruct or; simpl. apply agree_val_reg; auto. auto.
  eapply Mem.free_right_inject; eauto. eapply Mem.free_left_inject; eauto.
  (* show that no valid location points into the stack block being freed *)
  intros. inversion FB; subst.
  assert (PRIV': range_private F m' m'0 sp' (dstk ctx) f'.(fn_stacksize)).
    rewrite H8 in PRIV. eapply range_private_free_left; eauto. 
  rewrite DSTK in PRIV'. exploit (PRIV' (ofs + delta)). omega. intros [A B]. 
  eelim B; eauto. replace (ofs + delta - delta) with ofs by omega. 
  apply Mem.perm_max with k. apply Mem.perm_implies with p; auto with mem.

  (* inlined *)
  right. econstructor. split. simpl. omega. split. auto. 
  left. econstructor; eauto.
  eapply match_stacks_inside_invariant; eauto. 
    intros. eapply Mem.perm_free_3; eauto.
  destruct or; simpl. apply agree_val_reg; auto. auto.
  eapply Mem.free_left_inject; eauto.
  inv FB. rewrite H4 in PRIV. eapply range_private_free_left; eauto. 

(* (* internal function, not inlined *) *)
(*   assert (A: exists f', tr_function fenv f f' /\ fd' = Internal f').  *)
(*     Errors.monadInv FD. exists x. split; auto. eapply transf_function_spec; eauto.  *)
(*   destruct A as [f' [TR EQ]]. inversion TR; subst. *)
(*   exploit Mem.alloc_parallel_inject. eauto. eauto. apply Zle_refl.  *)
(*     instantiate (1 := fn_stacksize f'). inv H0. xomega.  *)
(*   intros [F' [m1' [sp' [A [B [C [D E]]]]]]]. *)
(*   left; econstructor; split. *)
(*   eapply plus_one. eapply exec_function_internal; eauto. *)
(*   rewrite H5. econstructor. *)
(*   instantiate (1 := F'). apply match_stacks_inside_base. *)
(*   assert (SP: sp' = Mem.nextblock m'0) by (eapply Mem.alloc_result; eauto). *)
(*   rewrite <- SP in MS0.  *)
(*   eapply match_stacks_invariant; eauto. *)
(*     intros. destruct (eq_block b1 stk).  *)
(*     subst b1. rewrite D in H7; inv H7. subst b2. eelim Plt_strict; eauto.   *)
(*     rewrite E in H7; auto.  *)
(*     intros. exploit Mem.perm_alloc_inv. eexact H. eauto.  *)
(*     destruct (eq_block b1 stk); intros; auto.  *)
(*     subst b1. rewrite D in H7; inv H7. subst b2. eelim Plt_strict; eauto.   *)
(*     intros. eapply Mem.perm_alloc_1; eauto.  *)
(*     intros. exploit Mem.perm_alloc_inv. eexact A. eauto.  *)
(*     rewrite dec_eq_false; auto. *)
(*   auto. auto. auto.  *)
(*   rewrite H4. apply agree_regs_init_regs. eauto. auto. inv H0; auto. congruence. auto. *)
(*   eapply Mem.valid_new_block; eauto. *)
(*   red; intros. split. *)
(*   eapply Mem.perm_alloc_2; eauto. inv H0; xomega. *)
(*   intros; red; intros. exploit Mem.perm_alloc_inv. eexact H. eauto. *)
(*   destruct (eq_block b stk); intros.  *)
(*   subst. rewrite D in H8; inv H8. inv H0; xomega. *)
(*   rewrite E in H8; auto. eelim Mem.fresh_block_alloc. eexact A. eapply Mem.mi_mappedblocks; eauto. *)
(*   auto. *)
(*   intros. exploit Mem.perm_alloc_inv; eauto. rewrite dec_eq_true. omega.  *)

(* internal function, inlined *)
  inversion FB; subst.
  exploit Mem.alloc_left_mapped_inject. 
    eauto.
    eauto.
    (* sp' is valid *)
    instantiate (1 := sp'). auto.
    (* offset is representable *)
    instantiate (1 := dstk ctx). generalize (Zmax2 (fn_stacksize f) 0). omega.
    (* size of target block is representable *)
    intros. right. exploit SSZ2; eauto with mem. inv FB; omega.
    (* we have full permissions on sp' at and above dstk ctx *)
    intros. apply Mem.perm_cur. apply Mem.perm_implies with Freeable; auto with mem.
    eapply range_private_perms; eauto. xomega.
    (* offset is aligned *)
    replace (fn_stacksize f - 0) with (fn_stacksize f) by omega.
    inv FB. apply min_alignment_sound; auto.
    (* nobody maps to (sp, dstk ctx...) *)
    intros. exploit (PRIV (ofs + delta')); eauto. xomega.
    intros [A B]. eelim B; eauto.
    replace (ofs + delta' - delta') with ofs by omega.
    apply Mem.perm_max with k. apply Mem.perm_implies with p; auto with mem.
  intros [F' [A [B [C D]]]].
  exploit tr_moves_init_regs; eauto. intros [rs'' [P [Q R]]].
  left; econstructor; econstructor; split. 
  eapply plus_left. eapply exec_Inop; eauto. eexact P. traceEq.
  left. econstructor.
  eapply match_stacks_inside_alloc_left; eauto.
  eapply match_stacks_inside_invariant; eauto.
  omega.
  eauto. auto.
  apply agree_regs_incr with F; auto.
  auto. auto. auto.
  rewrite H2. eapply range_private_alloc_left; eauto.
  auto. auto.

(* (* external function *) *)
(*   exploit match_stacks_globalenvs; eauto. intros [bound MG]. *)
(*   exploit external_call_mem_inject; eauto.  *)
(*     eapply match_globalenvs_preserves_globals; eauto. *)
(*   intros [F1 [v1 [m1' [A [B [C [D [E [J K]]]]]]]]]. *)
(*   simpl in FD. inv FD.  *)
(*   left; econstructor; split. *)
(*   eapply plus_one. eapply exec_function_external; eauto.  *)
(*     eapply external_call_symbols_preserved; eauto.  *)
(*     exact symbols_preserved. exact varinfo_preserved. *)
(*   econstructor. *)
(*     eapply match_stacks_bound with (Mem.nextblock m'0). *)
(*     eapply match_stacks_extcall with (F1 := F) (F2 := F1) (m1 := m) (m1' := m'0); eauto. *)
(*     intros; eapply external_call_max_perm; eauto.  *)
(*     intros; eapply external_call_max_perm; eauto. *)
(*     xomega. *)
(*     eapply external_call_nextblock; eauto.  *)
(*     auto. auto. *)

(* return fron noninlined function *)
  inv MS0.
  (* normal case *)
  left; econstructor; econstructor; split.
  eapply plus_one. eapply exec_return.
  left. econstructor; eauto. 
  apply match_stacks_inside_set_reg; auto. 
  apply agree_set_reg; auto.
  (* untailcall case *)
  inv MS; try congruence.
  rewrite RET in RET0; inv RET0.
(*
  assert (rpc = pc). unfold spc in H0; unfold node in *; xomega.
  assert (res0 = res). unfold sreg in H1; unfold reg in *; xomega.
  subst rpc res0.
*)
  left; econstructor; econstructor; split.
  eapply plus_one. eapply exec_return.
  left. eapply match_regular_states. 
  eapply match_stacks_inside_set_reg; eauto.
  eauto. auto. 
  apply agree_set_reg; auto.
  auto. auto. auto.
  red; intros. destruct (zlt ofs (dstk ctx)). apply PAD; omega. apply PRIV; omega.
  auto. auto. 
  
(* return from inlined function *)
  inv MS0; try congruence. rewrite RET0 in RET; inv RET. 
  unfold inline_return in AT. 
  assert (PRIV': range_private F m m' sp' (dstk ctx' + mstk ctx') f'.(fn_stacksize)).
    red; intros. destruct (zlt ofs (dstk ctx)). apply PAD. omega. apply PRIV. omega.
  destruct or.
  (* with a result *)
  left; econstructor; econstructor; split. 
  eapply plus_one. eapply exec_Iop; eauto. simpl. reflexivity. 
  left. econstructor; eauto. apply match_stacks_inside_set_reg; auto. apply agree_set_reg; auto.
  (* without a result *)
  left; econstructor; econstructor; split. 
  eapply plus_one. eapply exec_Inop; eauto.
  left. econstructor; eauto. subst vres. apply agree_set_reg_undef'; auto.
Qed.

Lemma transf_initial_states:
  forall st1, initial_state fprog st1 -> exists F st2, initial_state ftprog st2 /\ match_call F st1 st2.
Proof.
  intros. inv H.
  exploit funct_ptr_translated; eauto. intros [tf [FIND TR]].
  eexists. exists (Callstate nil tf nil m0); split.
  econstructor; eauto.
    erewrite (@program_lsim_init_mem_match Language_RTL Language_RTL); try apply transf_efT_sigT; eauto.
    unfold ge0 in *. erewrite symbols_preserved; eauto. 
    destruct Hfsim as [_ Hmain]. unfold fundef in *. simpl in *. rewrite <- Hmain. auto.
    rewrite <- H3. eapply sig_preserved; eauto. 
  econstructor; eauto. 
  instantiate (1 := Mem.flat_inj (Mem.nextblock m0)). 
  apply match_stacks_nil with (Mem.nextblock m0).
  constructor; intros. 
    unfold Mem.flat_inj. apply pred_dec_true; auto. 
    unfold Mem.flat_inj in H. destruct (plt b1 (Mem.nextblock m0)); congruence.
    eapply Genv.find_symbol_not_fresh; eauto.
    eapply Genv.find_funct_ptr_not_fresh; eauto.
    eapply Genv.find_var_info_not_fresh; eauto. 
    apply Ple_refl. 
  eapply Genv.initmem_inject; eauto.
Qed.

Lemma transf_final_states:
  forall F st1 st2 r, 
  match_states F st1 st2 -> final_state st1 r -> final_state st2 r.
Proof.
  intros. inv H0. inv H.
  exploit match_stacks_empty; eauto. intros EQ; subst. inv VINJ. constructor.
  exploit match_stacks_inside_empty; eauto. intros [A B]. congruence. 
Qed.

Inductive match_states_ext F st tst: Prop :=
| match_states_ext_intro
    (Hsrc: sound_state_ext fprog st)
    (Htgt: sound_state_ext ftprog tst)
    (Hmatch: match_states F st tst)
.

End FUTURE.

(* memory relation *)

Inductive mrelT_sem (mrel:meminj) (fprog ftprog:program) (i:WF.t) (s1 s2:state): Prop :=
| mrelT_sem_intro
    (MEASURE: i = WF.from_nat (measure s1))
    (Hsrc: sound_state_ext fprog s1)
    (Htgt: sound_state_ext ftprog s2)
    (MS: match_states fprog mrel s1 s2 \/ match_call fprog ftprog mrel s1 s2)
.

Definition mrelT_ops: mrelT_opsT Language_ext_RTL Language_ext_RTL meminj :=
  mkmrelT_opsT
    Language_ext_RTL Language_ext_RTL
    mrelT_sem
    (fun mrel v1 v2 => val_inject mrel v1 v2)
    (fun _ _ => True)
    (fun _ _ => True).

Lemma mrelT_ops_val_inject_list mrel v1 v2:
  val_list_inject mrel v1 v2 <-> list_forall2 (mrelT_ops.(sem_value) mrel) v1 v2.
Proof.
  revert v2.
  induction v1; intros; constructor; intro H; inv H; constructor; auto.
  - apply IHv1. auto.
  - apply IHv1. auto.
Qed.

Program Definition mrelT_props:
  @mrelT_propsT Language_ext_RTL Language_ext_RTL
                transf_sigT transf_efT transf_vT _ mrelT_ops :=
  mkmrelT_propsT _ _ _ _ _ _ _.
Next Obligation. repeat constructor. Qed.
Next Obligation. repeat constructor. Qed.
Next Obligation. inv H. auto. Qed.
Next Obligation.
  apply initial_state_equiv in H1. apply initial_state_equiv in H2.
  exploit transf_initial_states; eauto. intros [F [st2 [Hst2 Hmatch]]].
  exists F. eexists. constructor; eauto.
  { apply sound_initial. auto. }
  { apply sound_initial. auto. }
  right.
  inv H2. inv Hst2. unfold ge, ge0 in *.
  rewrite H in H2. inv H2. rewrite H0 in H5. inv H5. rewrite H3 in H6. inv H6.
  auto.
Qed.
Next Obligation.
  simpl in *. apply (mrelT_ops_val_inject_list mrel args1 args2) in Hargs.
  destruct fd1; inv Hfd1. destruct fd2; inv Hfd2.
  inv Hs0. inv Hmrel. destruct MS as [MS|MS]; inv MS.

  (* external function *)
  exploit match_stacks_globalenvs; eauto. intros [bound MG].
  exploit external_call_mem_inject; eauto.
    eapply match_globalenvs_preserves_globals; eauto.
    intros [F1 [v1 [m1'' [A [B [C [D [E [J K]]]]]]]]].
  eexists. eexists. eexists. eexists. eexists. exists F1. eexists.
  repeat (split; [eauto; fail|]). split.
  - econstructor. eapply external_call_symbols_preserved; eauto.
    + eapply symbols_preserved. apply Hp.
    + eapply varinfo_preserved. apply Hp.
  - split; auto.
    constructor; eauto.
    { eapply sound_past_step; eauto. econstructor. eauto. }
    { eapply sound_past_step; eauto. econstructor.
      eapply external_call_symbols_preserved; eauto.
      + eapply symbols_preserved. apply Hp.
      + eapply varinfo_preserved. apply Hp.
    }
    left. constructor; auto.
    eapply match_stacks_bound with (Mem.nextblock m2).
    eapply match_stacks_extcall with (F1 := mrel) (F2 := F1) (m1 := m1) (m1' := m2); eauto.
    intros; eapply external_call_max_perm; eauto.
    intros; eapply external_call_max_perm; eauto.
    xomega.
    eapply external_call_nextblock; eauto.
Qed.

Section STATE_LSIM.
  
Variable (fprog ftprog:program).
Hypothesis (Hfsim: @program_weak_lsim Language_RTL Language_RTL transf_sigT transf_efT transf_vT
                                      fprog ftprog).

Hypothesis (Hfprog: program_linkeq Language_RTL prog fprog).
Hypothesis (Hftprog: program_linkeq Language_RTL tprog ftprog).

Lemma match_states_state_lsim es es' (eF F:meminj) s1 s1'
      (MS: match_states_ext fprog ftprog F s1 s1'):
  @state_lsim Language_ext_RTL Language_ext_RTL transf_sigT _
              mrelT_ops fprog ftprog es es' eF F (WF.from_nat (measure s1)) s1 s1'.
Proof.
  revert F s1 s1' MS. pcofix CIH. intros F s1 s1' MS. pfold.
  inv MS. destruct (classic (exists r, final_state s1 r)).
  { destruct H as [rval Hrval]. eapply _state_lsim_term; eauto.
    - apply final_state_equiv. eauto.
    - apply final_state_equiv. eapply transf_final_states; eauto.
  }
  constructor; auto.
  { repeat intro. apply H. exists r0. apply final_state_equiv. auto. }
  intros. exploit step_simulation; eauto. simpl.
  intros [[F' [s2' [Hs2' Hmatch']]]|[mrel2 [Hmrel2 [Hevt Hmatch']]]].
  - eexists. exists s2'. exists F'.
    split; [auto|]. split; [auto|]. split; [constructor; auto|].
    { eapply sound_past_step; eauto. }
    { eapply sound_past_plus; eauto. }
    destruct Hmatch' as [Hmatch'|Hmatch'].
    + constructor. right. apply CIH; auto. constructor; auto.
      * eapply sound_past_step; eauto.
      * eapply sound_past_plus; eauto.
    + inversion Hmatch'. subst. eapply _state_lsim_or_csim_csim; eauto.
      { apply mrelT_ops_val_inject_list. auto. }
      { constructor; auto.
        - eapply sound_past_step; eauto.
        - eapply sound_past_plus; eauto.
      }
      intros. right. inv Hst2_mem. apply CIH.
      constructor; auto. econstructor; eauto.
      destruct MS0 as [MS0|MS0]; inv MS0; auto. 
      destruct MS0 as [MS0|MS0]; inv MS0; auto. 
  - subst. eexists. exists s1'. exists mrel2.
    split.
    { right. split; [apply star_refl|]. constructor. eauto. }
    split; [auto|]. split; [constructor; auto|].
    { eapply sound_past_step; eauto. }
    destruct Hmatch' as [Hmatch'|Hmatch'].
    + constructor. right. apply CIH; auto. constructor; auto.
      eapply sound_past_step; eauto.
    + inversion Hmatch'. subst. eapply _state_lsim_or_csim_csim; eauto.
      { apply mrelT_ops_val_inject_list. auto. }
      { constructor; auto.
        eapply sound_past_step; eauto.
      }
      intros. right. inv Hst2_mem. apply CIH.
      constructor; auto. econstructor; eauto.
      destruct MS0 as [MS0|MS0]; inv MS0; auto. 
      destruct MS0 as [MS0|MS0]; inv MS0; auto. 
Qed.

Lemma transf_function_lsim
      fenv (FENV: PTree_le fenv (funenv_program fprog))
      f f' (Hfd: Inlining.transf_function fenv f = OK f'):
  @function_lsim Language_ext_RTL Language_ext_RTL transf_sigT _
                 mrelT_ops fprog ftprog f f'.
Proof.
  constructor. repeat intro. inv Hmrel_entry.
  destruct MS as [MS|MS]; inv MS.
  pfold. constructor; auto.
  { intros ? Hfinal. apply final_state_equiv in Hfinal. inv Hfinal. }
  intros. destruct fd_src; inv Hfd_src. destruct fd_tgt; inv Hfd_tgt. inversion Hst2_src. subst.

  (* internal function, not inlined *)
  assert (TR: tr_function fenv f f'). 
    eapply transf_function_spec; eauto. 
  inversion TR; subst.
  exploit Mem.alloc_parallel_inject. eauto. eauto. apply Zle_refl. 
    instantiate (1 := fn_stacksize f'). inv H. xomega. 
  intros [F' [m1' [sp' [A [B [C [D E]]]]]]].
  eexists. eexists. eexists. split.
  left. eapply plus_one. eapply exec_function_internal; eauto.
  instantiate (2 := F'). split; [simpl; auto|].
  cut (match_states fprog F'
                    (State es_src f (Vptr stk Int.zero) (fn_entrypoint f)
                           (init_regs args_src (fn_params f)) m')
                    (State es_tgt f' (Vptr sp' Int.zero) (fn_entrypoint f')
                           (init_regs args_tgt (fn_params f')) m1')).
  { intro MS. split; [constructor; eauto|].
    { eapply sound_past_step; eauto. }
    { eapply sound_past_step; eauto. constructor; auto. }
    constructor. left. apply match_states_state_lsim. constructor; auto.
    - eapply sound_past_step; eauto.
    - eapply sound_past_step; eauto. constructor; auto.
  }
  rewrite H4. econstructor.
  apply match_stacks_inside_base.
  assert (SP: sp' = Mem.nextblock mem_entry_tgt) by (eapply Mem.alloc_result; eauto).
  rewrite <- SP in MS0.
  eapply match_stacks_invariant; eauto.
    intros. destruct (eq_block b1 stk).
    subst b1. rewrite D in H7; inv H7. subst b2. eelim Plt_strict; eauto.
    rewrite E in H7; auto.
    intros. exploit Mem.perm_alloc_inv. eexact H5. eauto.
    destruct (eq_block b1 stk); intros; auto.
    subst b1. rewrite D in H7; inv H7. subst b2. eelim Plt_strict; eauto.
    intros. eapply Mem.perm_alloc_1; eauto.
    intros. exploit Mem.perm_alloc_inv. eexact A. eauto.
    rewrite dec_eq_false; auto.
  auto. auto. auto. eauto. auto.
  rewrite H3. apply agree_regs_init_regs. eauto. auto. inv H; auto. congruence. auto.
  eapply Mem.valid_new_block; eauto.
  red; intros. split.
  eapply Mem.perm_alloc_2; eauto. inv H; xomega.
  intros; red; intros. exploit Mem.perm_alloc_inv. eexact H5. eauto.
  destruct (eq_block b stk); intros.
  subst. rewrite D in H8; inv H8. inv H; xomega.
  rewrite E in H8; auto. eelim Mem.fresh_block_alloc. eexact A. eapply Mem.mi_mappedblocks; eauto.
  auto.
  intros. exploit Mem.perm_alloc_inv; eauto. rewrite dec_eq_true. omega.
Qed.

End STATE_LSIM.

Lemma Inlining_program_lsim:
  @program_lsim Language_RTL Language_RTL transf_sigT transf_efT transf_vT
                (@function_lsim Language_ext_RTL Language_ext_RTL transf_sigT _ mrelT_ops)
                prog tprog.
Proof.
  generalize transf_function_lsim.
  destruct prog as [defs main]. simpl in *. simpl in *.
  unfold transf_program, transform_partial_program, transform_partial_program2 in TRANSF.
  Errors.monadInv TRANSF. rename x into tdefs.
  simpl in *. intro Hlsim. constructor; simpl; auto.
  revert Hlsim EQ.
  generalize tdefs at 2 as ftdefs.
  generalize defs at 1 3 as fdefs.
  revert defs tdefs.
  induction defs; simpl; intros tdefs fdefs ftdefs Hlsim Hglobdefs; inv Hglobdefs; try constructor.
  destruct a. destruct g.
  - match goal with
      | [H: match ?tf with | OK _ => _ | Error _ => _ end = _ |- _] => destruct tf eqn:Htf; inv H
    end.
    Errors.monadInv H1. constructor; simpl in *; try apply IHdefs; auto.
    split; auto. apply (@globdef_lsim_fun Language_RTL Language_RTL).
    destruct f; simpl in *.
    + Errors.monadInv Htf. constructor; simpl; intros.
      unfold Inlining.transf_function in EQ0.
      repeat match goal with
               | [H: context[let 'R _ _ _ := ?r:res in _] |- _] => destruct r eqn:Hr
               | [H: context[zlt ?a ?b] |- _] => destruct (zlt a b); inv H
             end.
      simpl. split; auto.
      repeat intro. exploit Hlsim; eauto.
      { apply program_linkeq_fenv_le. eauto. }
      unfold Inlining.transf_function.
      rewrite Hr. rewrite zlt_true; auto.
    + inv Htf.
      eapply globfun_lsim_intro; eauto; simpl; auto.
  - Errors.monadInv H0.
    constructor; simpl in *; try apply IHdefs; auto.
    split; auto. apply (@globdef_lsim_var Language_RTL Language_RTL).
    repeat constructor.
Qed.

End INLINING.
