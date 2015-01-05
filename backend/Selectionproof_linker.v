Require Import Classical.
Require Import Coqlib.
Require Import Maps Maps_linker.
Require Import AST.
Require Import Errors.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Language Linker Linkeq.
Require Import ProgramLSim FunctionLSim.
Require Import Switch.
Require Import Cminor.
Require Import Op.
Require Import CminorSel.
Require Import SelectOp.
Require Import SelectDiv.
Require Import SelectLong.
Require Import Selection.
Require Import SelectOpproof.
Require Import SelectDivproof.
Require Import SelectLongproof.
Require Import Selectionproof.
Require Import RTL_linker ValueAnalysis_linker.
Require Import WFType paco.

Local Open Scope cminorsel_scope.
Local Open Scope error_monad_scope.

Parameter hf: helper_functions.
Axiom Hget_helpers: forall ge, get_helpers ge = OK hf.

Lemma find_symbol_spec (p:Cminor.program) i:
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
  Ltac clarify :=
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
  induction (rev defs); simpl.
  { rewrite PTree.gempty. auto. }
  rewrite ? PTree.gsspec. destruct a. simpl. destruct (peq i i0); [subst|]; simpl.
  { destruct g; clarify.
    - apply Genv.genv_vars_range in H3. xomega.
    - apply Genv.genv_vars_range in H3. xomega.
    - apply Genv.genv_vars_range in H1. xomega.
    - apply Genv.genv_funs_range in H3. xomega.
    - apply Genv.genv_funs_range in H3. xomega.
    - apply Genv.genv_funs_range in H1. xomega.
  }
  { clarify.
    - apply Genv.genv_funs_range in H1. xomega.
    - apply Genv.genv_funs_range in H1. xomega.
    - apply Genv.genv_funs_range in H1. xomega.
    - apply Genv.genv_vars_range in H2. xomega.
    - apply Genv.genv_vars_range in H2. xomega.
    - apply Genv.genv_vars_range in H2. xomega.
  }
Qed.

Lemma classify_call_correct:
  forall prog fprog sp e m a v fd
         (Hle: program_linkeq Language_Cminor prog fprog),
  Cminor.eval_expr (Genv.globalenv fprog) sp e m a v ->
  Genv.find_funct (Genv.globalenv fprog) v = Some fd ->
  match classify_call (Genv.globalenv prog) a with
  | Call_default => True
  | Call_imm id => exists b, Genv.find_symbol (Genv.globalenv fprog) id = Some b /\ v = Vptr b Int.zero
  | Call_builtin ef => fd = External ef
  end.
Proof.
  intros. exploit classify_call_correct; eauto.
  unfold classify_call. destruct (expr_is_addrof_ident a) eqn:Hident; auto.
  destruct Hle as [Hle _]. unfold Cminor.fundef in *. simpl in *.
  generalize (find_symbol_spec fprog i).
  generalize (find_symbol_spec prog i).
  unfold Cminor.fundef in *.
  destruct (Genv.find_symbol (Genv.globalenv prog) i) as [b_src|] eqn:Hb_src.
  - match goal with
      | [|- context[match ?g with | Some _ => _ | None => _ end -> _]] =>
        let H := fresh "H" in destruct g as [g_src|] eqn:H; [|intro X; inv X]
    end.
    exploit (Hle i); [rewrite PTree_guespec; apply H1|]. intros [g_tgt [Hg_tgt Hsim]].
    rewrite PTree_guespec in Hg_tgt. unfold ident, Cminor.fundef in *. simpl in *. rewrite Hg_tgt.
    inv Hsim.
    + destruct (Genv.find_funct_ptr (Genv.globalenv prog) b_src) eqn:Hfd_src; [|intro X; inv X].
      destruct (Genv.find_var_info (Genv.globalenv prog) b_src) eqn:Hvi_src; [intro X; inv X|].
      intro. subst.
      destruct (Genv.find_symbol (Genv.globalenv fprog) i) eqn:Hb_tgt; [|intro X; inv X].
      destruct (Genv.find_funct_ptr (Genv.globalenv fprog) b) eqn:Hfd'_src; [|intro X; inv X].
      destruct (Genv.find_var_info (Genv.globalenv fprog) b) eqn:Hvi'_src; [intro X; inv X|].
      intro. subst.
      inv Hv; auto. inv H2.
      * destruct f; inv H3. destruct f0; inv H4. destruct e1; inv Hlinkable. auto.
      * destruct f; inv H3. destruct f0; inv H4. auto.
    + destruct (Genv.find_funct_ptr (Genv.globalenv prog) b_src) eqn:Hfd_src; [intro X; inv X|].
      destruct (Genv.find_var_info (Genv.globalenv prog) b_src) eqn:Hvi_src; [|intro X; inv X].
      intro. subst.
      destruct (Genv.find_symbol (Genv.globalenv fprog) i) eqn:Hb_tgt; [|intro X; inv X].
      destruct (Genv.find_funct_ptr (Genv.globalenv fprog) b) eqn:Hfd'_src; [intro X; inv X|].
      destruct (Genv.find_var_info (Genv.globalenv fprog) b) eqn:Hvi'_src; [|intro X; inv X].
      intros ? [b' [Hb' Hv']]. subst. rewrite Hb_tgt in Hb'. inv Hb'.
      eexists. split; eauto.
  - match goal with
      | [|- context[match ?g with | Some _ => _ | None => _ end -> _]] =>
        let H := fresh "H" in destruct g as [g_src|] eqn:H; intro X; inv X
    end.
    destruct (Genv.find_symbol (Genv.globalenv fprog) i) eqn:Hb_tgt.
    { match goal with
        | [|- context[match ?g with | Some _ => _ | None => _ end -> _]] =>
          let H := fresh "H" in destruct g as [g_tgt|] eqn:H; [|intro X; inv X]
      end.
      destruct g_tgt as [fd_tgt|vi_tgt].
      { destruct (Genv.find_funct_ptr (Genv.globalenv fprog) b) eqn:Hfd_tgt; [|intro X; inv X].
        destruct (Genv.find_var_info (Genv.globalenv fprog) b) eqn:Hvi_tgt; [intro X; inv X|].
        intro. subst. destruct f.
        { rewrite Hb_tgt. auto. }
        { destruct (ef_inline e0) eqn:Hinline.
          { intro. subst. eexists. split; eauto.
            destruct a; inv Hident. destruct c; inv H4. destruct (Int.eq i1 Int.zero); inv H5.
            destruct v; inv H0. destruct (Int.eq_dec i0 Int.zero); inv H4.
            inv H. inv H4. unfold Cminor.fundef in *. simpl in *. rewrite Hb_tgt in *.
            inv H0. auto.
          }
          { rewrite Hb_tgt. auto. }
        }
      }
      { destruct (Genv.find_funct_ptr (Genv.globalenv fprog) b); [intro X; inv X|].
        destruct (Genv.find_var_info (Genv.globalenv fprog) b) eqn:Hvi_tgt; [|intro X; inv X].
        intro. subst. rewrite Hb_tgt. auto.
      }
    }
    { rewrite Hb_tgt. auto. }
Qed.

Lemma Fundef_Cminor_funsig f: Fundef_sig (Fundef_common F_Cminor) f = Cminor.funsig f.
Proof. unfold Fundef_sig, Fundef_dec. simpl. destruct f; auto. Qed.
Lemma Fundef_CminorSel_funsig f: Fundef_sig (Fundef_common F_CminorSel) f = CminorSel.funsig f.
Proof. unfold Fundef_sig, Fundef_dec. simpl. destruct f; auto. Qed.

Definition transf_sigT := fun (sig:signature) => sig.
Definition transf_efT := fun (ef:external_function) => Errors.OK ef.
Definition transf_vT := fun (v:unit) => Errors.OK v.
Lemma transf_efT_sigT:
  forall (ef_src : efT Language_Cminor) (ef_tgt : efT Language_CminorSel),
    Errors.OK ef_src = OK ef_tgt ->
    id (EF_sig (efT Language_Cminor) ef_src) =
    EF_sig (efT Language_CminorSel) ef_tgt.
Proof. intros. inv H. auto. Qed.
Hint Resolve transf_efT_sigT.

Section PRESERVATION.

Variable prog: Cminor.program.
Variable tprog: CminorSel.program.
Hypothesis TRANSFPROG: transform_partial_program (sel_fundef hf (Genv.globalenv prog)) prog = OK tprog.

Section FUTURE.

Variable (fprog:Cminor.program).
Variable (ftprog:CminorSel.program).
Hypothesis (Hfsim: @program_weak_lsim Language_Cminor Language_CminorSel transf_sigT transf_efT transf_vT
                                      fprog ftprog).

Hypothesis (Hfprog: program_linkeq Language_Cminor prog fprog).
Hypothesis (Hftprog: program_linkeq Language_CminorSel tprog ftprog).

Let ge := Genv.globalenv fprog.
Let tge := Genv.globalenv ftprog.

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof.
  unfold ge, tge. eapply (@ProgramLSim.symbols_preserved Language_Cminor Language_CminorSel); eauto.
Qed.

Lemma function_ptr_translated:
  forall (b: block) (f: Cminor.fundef),
  Genv.find_funct_ptr ge b = Some f ->
  exists tf, Genv.find_funct_ptr tge b = Some tf /\
             globfun_weak_lsim Language_Cminor Language_CminorSel transf_sigT ge tge f tf.
Proof.  
  unfold ge, tge. intros. eapply (@ProgramLSim.funct_ptr_translated Language_Cminor Language_CminorSel); eauto.
Qed.

Lemma functions_translated:
  forall (v v': val) (f: Cminor.fundef),
  Genv.find_funct ge v = Some f ->
  Val.lessdef v v' ->
  exists tf, Genv.find_funct tge v' = Some tf /\
             globfun_weak_lsim Language_Cminor Language_CminorSel transf_sigT ge tge f tf.
Proof.  
  unfold ge, tge. intros. inv H0.
  - eapply (@ProgramLSim.functions_translated Language_Cminor Language_CminorSel); eauto.
  - inv H.
Qed.

Lemma sig_preserved:
  forall f tf,
    globfun_weak_lsim Language_Cminor Language_CminorSel id ge tge f tf ->
    CminorSel.funsig tf = Cminor.funsig f.
Proof.
  intros. inv H. inv Hsig. rewrite ? Fundef_Cminor_funsig, Fundef_CminorSel_funsig in Hsig0. auto.
Qed.

Lemma sig_function_translated:
  forall f tf, sel_fundef hf ge f = OK tf -> funsig tf = Cminor.funsig f.
Proof.
  intros. destruct f; monadInv H; auto. monadInv EQ. auto. 
Qed.

Lemma stackspace_function_translated:
  forall ge f tf, sel_function hf ge f = OK tf -> fn_stackspace tf = Cminor.fn_stackspace f.
Proof.
  intros. monadInv H. auto. 
Qed.

Lemma varinfo_preserved:
  forall b, Genv.find_var_info tge b = Genv.find_var_info ge b.
Proof.
  unfold ge, tge. intros.
  exploit (@ProgramLSim.varinfo_preserved Language_Cminor Language_CminorSel); eauto.
  instantiate (1 := b). unfold Cminor.fundef, fundef. simpl in *.
  repeat match goal with
           | [|- context[Genv.find_var_info ?ge ?b]] => destruct (Genv.find_var_info ge b)
         end;
    intro X; inv X; auto.
  destruct g0; auto.
Qed.

Lemma helper_implements_preserved:
  forall id sg vargs vres,
  helper_implements ge id sg vargs vres ->
  helper_implements tge id sg vargs vres.
Proof.
  admit.
  (* intros. destruct H as (b & ef & A & B & C & D). *)
  (* exploit function_ptr_translated; eauto. simpl. intros (tf & P & Q). inv Q. *)
  (* exists b; exists ef. *)
  (* split. rewrite symbols_preserved. auto. *)
  (* split. auto. *)
  (* split. auto. *)
  (* intros. eapply external_call_symbols_preserved; eauto. *)
  (* exact symbols_preserved. exact varinfo_preserved. *)
Qed.

Lemma builtin_implements_preserved:
  forall id sg vargs vres,
  builtin_implements ge id sg vargs vres ->
  builtin_implements tge id sg vargs vres.
Proof.
  unfold builtin_implements; intros.
  eapply external_call_symbols_preserved; eauto. 
  exact symbols_preserved. exact varinfo_preserved.
Qed.

Lemma helpers_correct_preserved:
  forall h, i64_helpers_correct ge h -> i64_helpers_correct tge h.
Proof.
  unfold i64_helpers_correct; intros.
  repeat (match goal with [ H: _ /\ _ |- _ /\ _ ] => destruct H; split end);
  intros; try (eapply helper_implements_preserved; eauto);
  try (eapply builtin_implements_preserved; eauto).
Qed.

Lemma HELPERS: i64_helpers_correct tge hf.
Proof.
  apply helpers_correct_preserved.
  apply get_helpers_correct.
  apply Hget_helpers.
Qed.
Hint Resolve HELPERS.

Section CMCONSTR.

Variable sp: val.
Variable e: env.
Variable m: mem.

Lemma eval_condexpr_of_expr:
  forall a le v b,
  eval_expr tge sp e m le a v ->
  Val.bool_of_val v b ->
  eval_condexpr tge sp e m le (condexpr_of_expr a) b.
Proof.
  intros until a. functional induction (condexpr_of_expr a); intros.
(* compare *)
  inv H. econstructor; eauto. 
  simpl in H6. inv H6. apply Val.bool_of_val_of_optbool. auto.
(* condition *)
  inv H. econstructor; eauto. destruct va; eauto.
(* let *)
  inv H. econstructor; eauto.
(* default *)
  econstructor. constructor. eauto. constructor. 
  simpl. inv H0. auto. auto. 
Qed.

Lemma eval_load:
  forall le a v chunk v',
  eval_expr tge sp e m le a v ->
  Mem.loadv chunk m v = Some v' ->
  eval_expr tge sp e m le (load chunk a) v'.
Proof.
  intros. generalize H0; destruct v; simpl; intro; try discriminate.
  unfold load. 
  generalize (eval_addressing _ _ _ _ _ chunk _ _ _ _ H (refl_equal _)).
  destruct (addressing chunk a). intros [vl [EV EQ]]. 
  eapply eval_Eload; eauto. 
Qed.

Lemma eval_store:
  forall chunk a1 a2 v1 v2 f k m',
  eval_expr tge sp e m nil a1 v1 ->
  eval_expr tge sp e m nil a2 v2 ->
  Mem.storev chunk m v1 v2 = Some m' ->
  step tge (State f (store chunk a1 a2) k sp e m)
        E0 (State f Sskip k sp e m').
Proof.
  intros. generalize H1; destruct v1; simpl; intro; try discriminate.
  unfold store.
  generalize (eval_addressing _ _ _ _ _ chunk _ _ _ _ H (refl_equal _)).
  destruct (addressing chunk a1). intros [vl [EV EQ]]. 
  eapply step_store; eauto. 
Qed.

(** Correctness of instruction selection for operators *)

Lemma eval_sel_unop:
  forall le op a1 v1 v,
  eval_expr tge sp e m le a1 v1 ->
  eval_unop op v1 = Some v ->
  exists v', eval_expr tge sp e m le (sel_unop hf op a1) v' /\ Val.lessdef v v'.
Proof.
  destruct op; simpl; intros; FuncInv; try subst v.
  apply eval_cast8unsigned; auto.
  apply eval_cast8signed; auto.
  apply eval_cast16unsigned; auto.
  apply eval_cast16signed; auto.
  apply eval_negint; auto.
  apply eval_notint; auto.
  apply eval_negf; auto.
  apply eval_absf; auto.
  apply eval_negfs; auto.
  apply eval_absfs; auto.
  apply eval_singleoffloat; auto.
  apply eval_floatofsingle; auto.
  eapply eval_intoffloat; eauto.
  eapply eval_intuoffloat; eauto.
  eapply eval_floatofint; eauto.
  eapply eval_floatofintu; eauto.
  eapply eval_intofsingle; eauto.
  eapply eval_intuofsingle; eauto.
  eapply eval_singleofint; eauto.
  eapply eval_singleofintu; eauto.
  eapply eval_negl; eauto.
  eapply eval_notl; eauto.
  eapply eval_intoflong; eauto.
  eapply eval_longofint; eauto.
  eapply eval_longofintu; eauto.
  eapply eval_longoffloat; eauto.
  eapply eval_longuoffloat; eauto.
  eapply eval_floatoflong; eauto.
  eapply eval_floatoflongu; eauto.
  eapply eval_longofsingle; eauto.
  eapply eval_longuofsingle; eauto.
  eapply eval_singleoflong; eauto.
  eapply eval_singleoflongu; eauto.
Qed.

Lemma eval_sel_binop:
  forall le op a1 a2 v1 v2 v,
  eval_expr tge sp e m le a1 v1 ->
  eval_expr tge sp e m le a2 v2 ->
  eval_binop op v1 v2 m = Some v ->
  exists v', eval_expr tge sp e m le (sel_binop hf op a1 a2) v' /\ Val.lessdef v v'.
Proof.
  destruct op; simpl; intros; FuncInv; try subst v.
  apply eval_add; auto.
  apply eval_sub; auto.
  apply eval_mul; auto.
  eapply eval_divs; eauto.
  eapply eval_divu; eauto.
  eapply eval_mods; eauto.
  eapply eval_modu; eauto.
  apply eval_and; auto.
  apply eval_or; auto.
  apply eval_xor; auto.
  apply eval_shl; auto.
  apply eval_shr; auto.
  apply eval_shru; auto.
  apply eval_addf; auto.
  apply eval_subf; auto.
  apply eval_mulf; auto.
  apply eval_divf; auto.
  apply eval_addfs; auto.
  apply eval_subfs; auto.
  apply eval_mulfs; auto.
  apply eval_divfs; auto.
  eapply eval_addl; eauto.
  eapply eval_subl; eauto.
  eapply eval_mull; eauto.
  eapply eval_divl; eauto.
  eapply eval_divlu; eauto.
  eapply eval_modl; eauto.
  eapply eval_modlu; eauto.
  eapply eval_andl; eauto.
  eapply eval_orl; eauto.
  eapply eval_xorl; eauto.
  eapply eval_shll; eauto.
  eapply eval_shrl; eauto.
  eapply eval_shrlu; eauto.
  apply eval_comp; auto.
  apply eval_compu; auto.
  apply eval_compf; auto.
  apply eval_compfs; auto.
  exists v; split; auto. eapply eval_cmpl; eauto.
  exists v; split; auto. eapply eval_cmplu; eauto.
Qed.

End CMCONSTR.

Section SEL_SWITCH.

Variable make_cmp_eq: expr -> Z -> expr.
Variable make_cmp_ltu: expr -> Z -> expr.
Variable make_sub: expr -> Z -> expr.
Variable make_to_int: expr -> expr.
Variable modulus: Z.
Variable R: Z -> val -> Prop.

Hypothesis eval_make_cmp_eq: forall sp e m le a v i n,
  eval_expr tge sp e m le a v -> R i v -> 0 <= n < modulus ->
  eval_expr tge sp e m le (make_cmp_eq a n) (Val.of_bool (zeq i n)).
Hypothesis eval_make_cmp_ltu: forall sp e m le a v i n,
  eval_expr tge sp e m le a v -> R i v -> 0 <= n < modulus ->
  eval_expr tge sp e m le (make_cmp_ltu a n) (Val.of_bool (zlt i n)).
Hypothesis eval_make_sub: forall sp e m le a v i n,
  eval_expr tge sp e m le a v -> R i v -> 0 <= n < modulus ->
  exists v', eval_expr tge sp e m le (make_sub a n) v' /\ R ((i - n) mod modulus) v'.
Hypothesis eval_make_to_int: forall sp e m le a v i,
  eval_expr tge sp e m le a v -> R i v ->
  exists v', eval_expr tge sp e m le (make_to_int a) v' /\ Rint (i mod Int.modulus) v'.

Lemma sel_switch_correct_rec:
  forall sp e m varg i x,
  R i varg ->
  forall t arg le,
  wf_comptree modulus t ->
  nth_error le arg = Some varg ->
  comptree_match modulus i t = Some x ->
  eval_exitexpr tge sp e m le (sel_switch make_cmp_eq make_cmp_ltu make_sub make_to_int arg t) x.
Proof.
  intros until x; intros Ri. induction t; simpl; intros until le; intros WF ARG MATCH.
- (* base case *)
  inv MATCH. constructor.
- (* eq test *)
  inv WF.
  assert (eval_expr tge sp e m le (make_cmp_eq (Eletvar arg) key) (Val.of_bool (zeq i key))).
  { eapply eval_make_cmp_eq; eauto. constructor; auto. }
  eapply eval_XEcondition with (va := zeq i key). 
  eapply eval_condexpr_of_expr; eauto. destruct (zeq i key); constructor; auto. 
  destruct (zeq i key); simpl. 
  + inv MATCH. constructor.
  + eapply IHt; eauto.
- (* lt test *)
  inv WF.
  assert (eval_expr tge sp e m le (make_cmp_ltu (Eletvar arg) key) (Val.of_bool (zlt i key))).
  { eapply eval_make_cmp_ltu; eauto. constructor; auto. }
  eapply eval_XEcondition with (va := zlt i key). 
  eapply eval_condexpr_of_expr; eauto. destruct (zlt i key); constructor; auto. 
  destruct (zlt i key); simpl. 
  + eapply IHt1; eauto.
  + eapply IHt2; eauto.
- (* jump table *)
  inv WF.
  exploit (eval_make_sub sp e m le). eapply eval_Eletvar. eauto. eauto.
  instantiate (1 := ofs). auto.
  intros (v' & A & B).
  set (i' := (i - ofs) mod modulus) in *.
  assert (eval_expr tge sp e m (v' :: le) (make_cmp_ltu (Eletvar O) sz) (Val.of_bool (zlt i' sz))).
  { eapply eval_make_cmp_ltu; eauto. constructor; auto. }
  econstructor. eauto. 
  eapply eval_XEcondition with (va := zlt i' sz).
  eapply eval_condexpr_of_expr; eauto. destruct (zlt i' sz); constructor; auto.
  destruct (zlt i' sz); simpl.
  + exploit (eval_make_to_int sp e m (v' :: le) (Eletvar O)).
    constructor. simpl; eauto. eauto. intros (v'' & C & D). inv D. 
    econstructor; eauto. congruence. 
  + eapply IHt; eauto.
Qed.

Lemma sel_switch_correct:
  forall dfl cases arg sp e m varg i t le,
  validate_switch modulus dfl cases t = true ->
  eval_expr tge sp e m le arg varg ->
  R i varg ->
  0 <= i < modulus ->
  eval_exitexpr tge sp e m le
     (XElet arg (sel_switch make_cmp_eq make_cmp_ltu make_sub make_to_int O t))
     (switch_target i dfl cases).
Proof.
  intros. exploit validate_switch_correct; eauto. omega. intros [A B].
  econstructor. eauto. eapply sel_switch_correct_rec; eauto.
Qed.

End SEL_SWITCH.

Lemma sel_switch_int_correct:
  forall dfl cases arg sp e m i t le,
  validate_switch Int.modulus dfl cases t = true ->
  eval_expr tge sp e m le arg (Vint i) ->
  eval_exitexpr tge sp e m le (XElet arg (sel_switch_int O t)) (switch_target (Int.unsigned i) dfl cases).
Proof.
  assert (INTCONST: forall n sp e m le, 
            eval_expr tge sp e m le (Eop (Ointconst n) Enil) (Vint n)).
  { intros. econstructor. constructor. auto. } 
  intros. eapply sel_switch_correct with (R := Rint); eauto.
- intros until n; intros EVAL R RANGE.
  exploit eval_comp. eexact EVAL. apply (INTCONST (Int.repr n)).  
  instantiate (1 := Ceq). intros (vb & A & B). 
  inv R. unfold Val.cmp in B. simpl in B. revert B. 
  predSpec Int.eq Int.eq_spec n0 (Int.repr n); intros B; inv B. 
  rewrite Int.unsigned_repr. unfold proj_sumbool; rewrite zeq_true; auto. 
  unfold Int.max_unsigned; omega.
  unfold proj_sumbool; rewrite zeq_false; auto.
  red; intros; elim H1. rewrite <- (Int.repr_unsigned n0). congruence.
- intros until n; intros EVAL R RANGE.
  exploit eval_compu. eexact EVAL. apply (INTCONST (Int.repr n)).  
  instantiate (1 := Clt). intros (vb & A & B). 
  inv R. unfold Val.cmpu in B. simpl in B.
  unfold Int.ltu in B. rewrite Int.unsigned_repr in B. 
  destruct (zlt (Int.unsigned n0) n); inv B; auto. 
  unfold Int.max_unsigned; omega.
- intros until n; intros EVAL R RANGE.
  exploit eval_sub. eexact EVAL. apply (INTCONST (Int.repr n)). intros (vb & A & B).
  inv R. simpl in B. inv B. econstructor; split; eauto. 
  replace ((Int.unsigned n0 - n) mod Int.modulus)
     with (Int.unsigned (Int.sub n0 (Int.repr n))).
  constructor.
  unfold Int.sub. rewrite Int.unsigned_repr_eq. f_equal. f_equal. 
  apply Int.unsigned_repr. unfold Int.max_unsigned; omega.
- intros until i0; intros EVAL R. exists v; split; auto. 
  inv R. rewrite Zmod_small by (apply Int.unsigned_range). constructor.
- constructor. 
- apply Int.unsigned_range.
Qed.

Lemma sel_switch_long_correct:
  forall dfl cases arg sp e m i t le,
  validate_switch Int64.modulus dfl cases t = true ->
  eval_expr tge sp e m le arg (Vlong i) ->
  eval_exitexpr tge sp e m le (XElet arg (sel_switch_long hf O t)) (switch_target (Int64.unsigned i) dfl cases).
Proof.
  intros. eapply sel_switch_correct with (R := Rlong); eauto.
- intros until n; intros EVAL R RANGE.
  eapply eval_cmpl. eexact EVAL. apply eval_longconst with (n := Int64.repr n).
  inv R. unfold Val.cmpl. simpl. f_equal; f_equal. unfold Int64.eq. 
  rewrite Int64.unsigned_repr. destruct (zeq (Int64.unsigned n0) n); auto. 
  unfold Int64.max_unsigned; omega.
- intros until n; intros EVAL R RANGE. 
  eapply eval_cmplu. eexact EVAL. apply eval_longconst with (n := Int64.repr n).
  inv R. unfold Val.cmplu. simpl. f_equal; f_equal. unfold Int64.ltu. 
  rewrite Int64.unsigned_repr. destruct (zlt (Int64.unsigned n0) n); auto. 
  unfold Int64.max_unsigned; omega.
- intros until n; intros EVAL R RANGE.
  exploit eval_subl. eexact HELPERS. eexact EVAL. apply eval_longconst with (n := Int64.repr n).
  intros (vb & A & B).
  inv R. simpl in B. inv B. econstructor; split; eauto. 
  replace ((Int64.unsigned n0 - n) mod Int64.modulus)
     with (Int64.unsigned (Int64.sub n0 (Int64.repr n))).
  constructor.
  unfold Int64.sub. rewrite Int64.unsigned_repr_eq. f_equal. f_equal. 
  apply Int64.unsigned_repr. unfold Int64.max_unsigned; omega.
- intros until i0; intros EVAL R. 
  exploit eval_lowlong. eexact EVAL. intros (vb & A & B). 
  inv R. simpl in B. inv B. econstructor; split; eauto.
  replace (Int64.unsigned n mod Int.modulus) with (Int.unsigned (Int64.loword n)).
  constructor.
  unfold Int64.loword. apply Int.unsigned_repr_eq. 
- constructor. 
- apply Int64.unsigned_range.
Qed.

(** Compatibility of evaluation functions with the "less defined than" relation. *)

Ltac TrivialExists :=
  match goal with
  | [ |- exists v, Some ?x = Some v /\ _ ] => exists x; split; auto
  | _ => idtac
  end.

Lemma eval_unop_lessdef:
  forall op v1 v1' v,
  eval_unop op v1 = Some v -> Val.lessdef v1 v1' ->
  exists v', eval_unop op v1' = Some v' /\ Val.lessdef v v'.
Proof.
  intros until v; intros EV LD. inv LD. 
  exists v; auto.
  destruct op; simpl in *; inv EV; TrivialExists.
Qed.

Lemma eval_binop_lessdef:
  forall op v1 v1' v2 v2' v m m',
  eval_binop op v1 v2 m = Some v -> 
  Val.lessdef v1 v1' -> Val.lessdef v2 v2' -> Mem.extends m m' ->
  exists v', eval_binop op v1' v2' m' = Some v' /\ Val.lessdef v v'.
Proof.
  intros until m'; intros EV LD1 LD2 ME.
  assert (exists v', eval_binop op v1' v2' m = Some v' /\ Val.lessdef v v').
  inv LD1. inv LD2. exists v; auto. 
  destruct op; destruct v1'; simpl in *; inv EV; TrivialExists.
  destruct op; simpl in *; inv EV; TrivialExists.
  destruct op; try (exact H). 
  simpl in *. TrivialExists. inv EV. apply Val.of_optbool_lessdef. 
  intros. apply Val.cmpu_bool_lessdef with (Mem.valid_pointer m) v1 v2; auto.
  intros; eapply Mem.valid_pointer_extends; eauto.
Qed.

(** * Semantic preservation for instruction selection. *)

(** Semantic preservation for expressions. *)

Lemma sel_expr_correct:
  forall sp e m a v,
  Cminor.eval_expr ge sp e m a v ->
  forall e' le m',
  env_lessdef e e' -> Mem.extends m m' ->
  exists v', eval_expr tge sp e' m' le (sel_expr hf a) v' /\ Val.lessdef v v'.
Proof.
  induction 1; intros; simpl.
  (* Evar *)
  exploit H0; eauto. intros [v' [A B]]. exists v'; split; auto. constructor; auto.
  (* Econst *)
  destruct cst; simpl in *; inv H. 
  exists (Vint i); split; auto. econstructor. constructor. auto. 
  exists (Vfloat f); split; auto. econstructor. constructor. auto.
  exists (Vsingle f); split; auto. econstructor. constructor. auto. 
  exists (Val.longofwords (Vint (Int64.hiword i)) (Vint (Int64.loword i))); split.
  eapply eval_Eop. constructor. EvalOp. simpl; eauto. constructor. EvalOp. simpl; eauto. constructor. auto.
  simpl. rewrite Int64.ofwords_recompose. auto.
  rewrite <- symbols_preserved. fold (Genv.symbol_address tge i i0). apply eval_addrsymbol.
  apply eval_addrstack.
  (* Eunop *)
  exploit IHeval_expr; eauto. intros [v1' [A B]].
  exploit eval_unop_lessdef; eauto. intros [v' [C D]].
  exploit eval_sel_unop; eauto. intros [v'' [E F]].
  exists v''; split; eauto. eapply Val.lessdef_trans; eauto. 
  (* Ebinop *)
  exploit IHeval_expr1; eauto. intros [v1' [A B]].
  exploit IHeval_expr2; eauto. intros [v2' [C D]].
  exploit eval_binop_lessdef; eauto. intros [v' [E F]].
  exploit eval_sel_binop. eexact A. eexact C. eauto. intros [v'' [P Q]].
  exists v''; split; eauto. eapply Val.lessdef_trans; eauto. 
  (* Eload *)
  exploit IHeval_expr; eauto. intros [vaddr' [A B]].
  exploit Mem.loadv_extends; eauto. intros [v' [C D]].
  exists v'; split; auto. eapply eval_load; eauto.
Qed.

Lemma sel_exprlist_correct:
  forall sp e m a v,
  Cminor.eval_exprlist ge sp e m a v ->
  forall e' le m',
  env_lessdef e e' -> Mem.extends m m' ->
  exists v', eval_exprlist tge sp e' m' le (sel_exprlist hf a) v' /\ Val.lessdef_list v v'.
Proof.
  induction 1; intros; simpl. 
  exists (@nil val); split; auto. constructor.
  exploit sel_expr_correct; eauto. intros [v1' [A B]].
  exploit IHeval_exprlist; eauto. intros [vl' [C D]].
  exists (v1' :: vl'); split; auto. constructor; eauto.
Qed.

(** Semantic preservation for functions and statements. *)

Inductive match_cont: Cminor.cont -> CminorSel.cont -> Prop :=
  | match_cont_stop:
      match_cont Cminor.Kstop Kstop
  | match_cont_seq: forall s s' k k' prog,
      program_linkeq Language_Cminor prog fprog ->
      sel_stmt hf (Genv.globalenv prog) s = OK s' ->
      match_cont k k' ->
      match_cont (Cminor.Kseq s k) (Kseq s' k')
  | match_cont_block: forall k k',
      match_cont k k' ->
      match_cont (Cminor.Kblock k) (Kblock k')
  | match_cont_call: forall id f sp e k f' e' k' prog,
      program_linkeq Language_Cminor prog fprog ->
      sel_function hf (Genv.globalenv prog) f = OK f' ->
      match_cont k k' -> env_lessdef e e' ->
      match_cont (Cminor.Kcall id f sp e k) (Kcall id f' sp e' k').

Inductive match_states: Cminor.state -> CminorSel.state -> Prop :=
  | match_state: forall f f' s k s' k' sp e m e' m' prog1 prog2
        (PROG1: program_linkeq Language_Cminor prog1 fprog)
        (PROG2: program_linkeq Language_Cminor prog2 fprog)
        (TF: sel_function hf (Genv.globalenv prog1) f = OK f')
        (TS: sel_stmt hf (Genv.globalenv prog2) s = OK s')
        (MC: match_cont k k')
        (LD: env_lessdef e e')
        (ME: Mem.extends m m'),
      match_states
        (Cminor.State f s k sp e m)
        (State f' s' k' sp e' m')
  | match_returnstate: forall v v' k k' m m'
        (MC: match_cont k k')
        (LD: Val.lessdef v v')
        (ME: Mem.extends m m'),
      match_states
        (Cminor.Returnstate v k m)
        (Returnstate v' k' m')
  | match_builtin_1: forall ef args args' optid f sp e k m al f' e' k' m' prog
        (PROG: program_linkeq Language_Cminor prog fprog)
        (TF: sel_function hf (Genv.globalenv prog) f = OK f')
        (MC: match_cont k k')
        (LDA: Val.lessdef_list args args')
        (LDE: env_lessdef e e')
        (ME: Mem.extends m m')
        (EA: eval_exprlist tge sp e' m' nil al args'),
      match_states
        (Cminor.Callstate (External ef) args (Cminor.Kcall optid f sp e k) m)
        (State f' (Sbuiltin optid ef al) k' sp e' m')
  | match_builtin_2: forall v v' optid f sp e k m f' e' m' k' prog
        (PROG: program_linkeq Language_Cminor prog fprog)
        (TF: sel_function hf (Genv.globalenv prog) f = OK f')
        (MC: match_cont k k')
        (LDV: Val.lessdef v v')
        (LDE: env_lessdef e e')
        (ME: Mem.extends m m'),
      match_states
        (Cminor.Returnstate v (Cminor.Kcall optid f sp e k) m)
        (State f' Sskip k' sp (set_optvar optid v' e') m').

Inductive match_call: Cminor.state -> CminorSel.state -> Prop :=
  | match_callstate: forall f f' args args' k k' m m'
        (TF: globfun_weak_lsim Language_Cminor Language_CminorSel transf_sigT ge tge f f')
        (MC: match_cont k k')
        (LD: Val.lessdef_list args args')
        (ME: Mem.extends m m'),
      match_call
        (Cminor.Callstate f args k m)
        (Callstate f' args' k' m').

Remark call_cont_commut:
  forall k k', match_cont k k' -> match_cont (Cminor.call_cont k) (call_cont k').
Proof.
  induction 1; simpl; auto. constructor. econstructor; eauto.
Qed.

Remark find_label_commut:
  forall prog (Hprog: program_linkeq Language_Cminor prog fprog) lbl s k s' k',
  match_cont k k' ->
  sel_stmt hf (Genv.globalenv prog) s = OK s' ->
  match Cminor.find_label lbl s k, find_label lbl s' k' with
  | None, None => True
  | Some(s1, k1), Some(s1', k1') => sel_stmt hf (Genv.globalenv prog) s1 = OK s1' /\ match_cont k1 k1'
  | _, _ => False
  end.
Proof.
  induction s; intros until k'; simpl; intros MC SE; try (monadInv SE); simpl; auto.
(* store *)
  unfold store. destruct (addressing m (sel_expr hf e)); simpl; auto.
(* call *)
  unfold Cminor.fundef in *. simpl in *.
  destruct (classify_call (Genv.globalenv prog0) e); simpl; auto.
(* tailcall *)
  unfold Cminor.fundef in *. simpl in *.
  destruct (classify_call (Genv.globalenv prog0) e); simpl; auto.
(* seq *)
  exploit (IHs1 (Cminor.Kseq s2 k)). econstructor; eauto. eauto.  
  destruct (Cminor.find_label lbl s1 (Cminor.Kseq s2 k)) as [[sx kx] | ];
  destruct (find_label lbl x (Kseq x0 k')) as [[sy ky] | ];
  intuition. apply IHs2; auto.
(* ifthenelse *)
  exploit (IHs1 k); eauto. 
  destruct (Cminor.find_label lbl s1 k) as [[sx kx] | ];
  destruct (find_label lbl x k') as [[sy ky] | ];
  intuition. apply IHs2; auto.
(* loop *)
  apply IHs. econstructor; eauto. simpl; rewrite EQ; auto. auto.
(* block *)
  apply IHs. constructor; auto. auto.
(* switch *)
  destruct b. 
  destruct (validate_switch Int64.modulus n l (compile_switch Int64.modulus n l)); inv SE.
  simpl; auto.
  destruct (validate_switch Int.modulus n l (compile_switch Int.modulus n l)); inv SE.
  simpl; auto.
(* return *)
  destruct o; inv SE; simpl; auto.
(* label *)
  destruct (ident_eq lbl l). auto. apply IHs; auto.
Qed.

Lemma sel_step_correct:
  forall S1 t S2, Cminor.step ge S1 t S2 ->
  forall T1, match_states S1 T1 ->
  (exists T2, step tge T1 t T2 /\ (match_states S2 T2 \/ match_call S2 T2))
  \/ (measure S2 < measure S1 /\ t = E0 /\ (match_states S2 T1 \/ match_call S2 T1))%nat.
Proof.
  induction 1; intros T1 ME; inv ME; try (monadInv TS).
- (* skip seq *)
  inv MC. left; econstructor; split. econstructor. left. econstructor; try apply TF; try apply H2; eauto.
- (* skip block *)
  inv MC. left; econstructor; split. econstructor. left. econstructor; try apply TF; eauto.
- (* skip call *)
  exploit Mem.free_parallel_extends; eauto. intros [m2' [A B]].
  left; econstructor; split. 
  econstructor. inv MC; simpl in H; simpl; auto. 
  eauto. 
  erewrite stackspace_function_translated; eauto. 
  left. constructor; auto.
- (* assign *)
  exploit sel_expr_correct; eauto. intros [v' [A B]].
  left; econstructor; split.
  econstructor; eauto.
  left. econstructor; try apply TF; eauto. apply set_var_lessdef; auto.
- (* store *)
  exploit sel_expr_correct. eexact H. eauto. eauto. intros [vaddr' [A B]].
  exploit sel_expr_correct. eexact H0. eauto. eauto. intros [v' [C D]].
  exploit Mem.storev_extends; eauto. intros [m2' [P Q]].
  left; econstructor; split.
  eapply eval_store; eauto.
  left. econstructor; try apply TF; eauto.
- (* Scall *)
  exploit sel_exprlist_correct; eauto. intros [vargs' [C D]].
  exploit classify_call_correct; eauto. 
  unfold Cminor.fundef in *. simpl in *.
  destruct (classify_call (Genv.globalenv prog2) a) as [ | id | ef].
+ (* indirect *)
  exploit sel_expr_correct; eauto. intros [vf' [A B]].
  exploit functions_translated; eauto. intros (fd' & U & V).
  left; econstructor; split.
  econstructor; eauto. econstructor; eauto. 
  apply sig_preserved; auto.
  right. econstructor; eauto. econstructor; try apply TF; eauto.
+ (* direct *)
  intros [b [U V]]. 
  exploit functions_translated; eauto. intros (fd' & X & Y).
  left; econstructor; split.
  econstructor; eauto.
  subst vf. econstructor; eauto. rewrite symbols_preserved; eauto.
  apply sig_preserved; auto.
  right. econstructor; eauto. econstructor; try apply TF; eauto.
+ (* turned into Sbuiltin *)
  intros EQ. subst fd. 
  right; split. simpl. omega. split. auto. 
  left. econstructor; try apply TF; eauto.
- (* Stailcall *)
  exploit Mem.free_parallel_extends; eauto. intros [m2' [P Q]].
  erewrite <- stackspace_function_translated in P by eauto.
  exploit sel_expr_correct; eauto. intros [vf' [A B]].
  exploit sel_exprlist_correct; eauto. intros [vargs' [C D]].
  exploit functions_translated; eauto. intros [fd' [E F]].
  left; econstructor; split.
  exploit classify_call_correct; eauto. 
  unfold Cminor.fundef in *. simpl in *.
  destruct (classify_call (Genv.globalenv prog2) a) as [ | id | ef]; intros. 
  econstructor; eauto. econstructor; eauto. apply sig_preserved; auto.
  destruct H2 as [b [U V]]. subst vf. inv B. 
  econstructor; eauto. econstructor; eauto. rewrite symbols_preserved; eauto. apply sig_preserved; auto.
  econstructor; eauto. econstructor; eauto. apply sig_preserved; auto.
  right. econstructor; eauto. apply call_cont_commut; auto.
- (* Sbuiltin *)
  exploit sel_exprlist_correct; eauto. intros [vargs' [P Q]].
  exploit external_call_mem_extends; eauto. 
  intros [vres' [m2 [A [B [C D]]]]].
  left; econstructor; split.
  econstructor. eauto. eapply external_call_symbols_preserved; eauto.
  exact symbols_preserved. exact varinfo_preserved.
  left. econstructor; try apply TF; eauto.
  destruct optid; simpl; auto. apply set_var_lessdef; auto.
- (* Seq *)
  left; econstructor; split.
  constructor. left. econstructor; try apply TF; eauto. econstructor; eauto.
- (* Sifthenelse *)
  exploit sel_expr_correct; eauto. intros [v' [A B]].
  assert (Val.bool_of_val v' b). inv B. auto. inv H0.
  left; exists (State f' (if b then x else x0) k' sp e' m'); split.
  econstructor; eauto. eapply eval_condexpr_of_expr; eauto. 
  left. econstructor; try apply TF; eauto. destruct b; auto.
- (* Sloop *)
  left; econstructor; split. constructor. left. econstructor; try apply TF; eauto.
  econstructor; eauto. simpl; rewrite EQ; auto.
- (* Sblock *)
  left; econstructor; split. constructor. left. econstructor; try apply TF; eauto. constructor; auto.
- (* Sexit seq *)
  inv MC. left; econstructor; split. constructor. left. econstructor; try apply TF; eauto.
- (* Sexit0 block *)
  inv MC. left; econstructor; split. constructor. left. econstructor; try apply TF; eauto.
- (* SexitS block *)
  inv MC. left; econstructor; split. constructor. left. econstructor; try apply TF; eauto.
- (* Sswitch *)
  inv H0; simpl in TS.
+ set (ct := compile_switch Int.modulus default cases) in *.
  destruct (validate_switch Int.modulus default cases ct) eqn:VALID; inv TS.
  exploit sel_expr_correct; eauto. intros [v' [A B]]. inv B.
  left; econstructor; split. 
  econstructor. eapply sel_switch_int_correct; eauto. 
  left. econstructor; try apply TF; eauto.
+ set (ct := compile_switch Int64.modulus default cases) in *.
  destruct (validate_switch Int64.modulus default cases ct) eqn:VALID; inv TS.
  exploit sel_expr_correct; eauto. intros [v' [A B]]. inv B.
  left; econstructor; split.
  econstructor. eapply sel_switch_long_correct; eauto. 
  left. econstructor; try apply TF; eauto.
- (* Sreturn None *)
  exploit Mem.free_parallel_extends; eauto. intros [m2' [P Q]].
  erewrite <- stackspace_function_translated in P by eauto.
  left; econstructor; split. 
  econstructor. simpl; eauto. 
  left. constructor; auto. apply call_cont_commut; auto.
- (* Sreturn Some *)
  exploit Mem.free_parallel_extends; eauto. intros [m2' [P Q]].
  erewrite <- stackspace_function_translated in P by eauto.
  exploit sel_expr_correct; eauto. intros [v' [A B]].
  left; econstructor; split. 
  econstructor; eauto.
  left. constructor; auto. apply call_cont_commut; auto.
- (* Slabel *)
  left; econstructor; split. constructor. left. econstructor; try apply TF; eauto.
- (* Sgoto *)
  assert (sel_stmt hf (Genv.globalenv prog1) (Cminor.fn_body f) = OK (fn_body f')).
  { unfold sel_function in TF. monadInv TF; simpl; auto. }
  exploit (find_label_commut prog1 PROG1 lbl (Cminor.fn_body f) (Cminor.call_cont k)).
    apply call_cont_commut; eauto. eauto.
  rewrite H. 
  destruct (find_label lbl (fn_body f') (call_cont k'0))
  as [[s'' k'']|] eqn:?; intros; try contradiction.
  destruct H1. 
  left; econstructor; split.
  econstructor; eauto. 
  left. econstructor; try apply TF; try apply H1; eauto.
(* - (* internal function *) *)
(*   monadInv TF. generalize EQ; intros TF; monadInv TF. *)
(*   exploit Mem.alloc_extends. eauto. eauto. apply Zle_refl. apply Zle_refl.  *)
(*   intros [m2' [A B]]. *)
(*   left; econstructor; split. *)
(*   econstructor; simpl; eauto. *)
(*   constructor; simpl; auto. apply set_locals_lessdef. apply set_params_lessdef; auto. *)
(* - (* external call *) *)
(*   monadInv TF. *)
(*   exploit external_call_mem_extends; eauto.  *)
(*   intros [vres' [m2 [A [B [C D]]]]]. *)
(*   left; econstructor; split. *)
(*   econstructor. eapply external_call_symbols_preserved; eauto. *)
(*   exact symbols_preserved. exact varinfo_preserved. *)
(*   constructor; auto. *)
- (* external call turned into a Sbuiltin *)
  exploit external_call_mem_extends; eauto. 
  intros [vres' [m2 [A [B [C D]]]]].
  left; econstructor; split.
  econstructor. eauto. eapply external_call_symbols_preserved; eauto.
  exact symbols_preserved. exact varinfo_preserved.
  left. econstructor; try apply TF; auto.
- (* return *)
  inv MC. 
  left; econstructor; split. 
  econstructor. 
  left. econstructor; try apply H6; eauto. destruct optid; simpl; auto. apply set_var_lessdef; auto.
- (* return of an external call turned into a Sbuiltin *)
  right; split. simpl; omega. split. auto. left. econstructor; try apply TF; eauto. 
  destruct optid; simpl; auto. apply set_var_lessdef; auto.
Qed.

Lemma sel_initial_states:
  forall S, Cminor.initial_state fprog S ->
  exists R, initial_state ftprog R /\ match_call S R.
Proof.
  induction 1.
  exploit function_ptr_translated; eauto. intros (f' & A & B).
  econstructor; split.
  econstructor.
  eapply (@ProgramLSim.program_lsim_init_mem_match Language_Cminor Language_CminorSel); eauto.
  rewrite symbols_preserved.
  replace (prog_main ftprog) with (prog_main fprog).
  unfold ge, ge0 in *. eauto.
  destruct Hfsim as [_ Hmain]. unfold fundef in *. simpl in *. rewrite <- Hmain. auto.
  eauto.
  rewrite <- H2. apply sig_preserved; auto.
  econstructor; eauto. constructor. apply Mem.extends_refl.
Qed.

Lemma sel_final_states:
  forall S R r,
  match_states S R -> Cminor.final_state S r -> final_state R r.
Proof.
  intros. inv H0. inv H. inv MC. inv LD. constructor.
Qed.

End FUTURE.

(* memory relation *)

Inductive mrelT_sem (mrel:unit) (fprog:Cminor.program) (ftprog:CminorSel.program) (i:WF.t) (s1:Cminor.state) (s2:CminorSel.state): Prop :=
| mrelT_sem_intro
    (MEASURE: i = WF.from_nat (measure s1))
    (MS: match_states fprog ftprog s1 s2 \/ match_call fprog ftprog s1 s2)
.

Definition mrelT_ops: mrelT_opsT Language_ext_Cminor Language_ext_CminorSel unit :=
  mkmrelT_opsT
    Language_ext_Cminor Language_ext_CminorSel
    mrelT_sem
    (fun _ v1 v2 => Val.lessdef v1 v2)
    (fun _ _ => True)
    (fun _ _ => True).

Lemma mrelT_ops_lessdef_list mrel v1 v2:
  Val.lessdef_list v1 v2 <-> list_forall2 (mrelT_ops.(sem_value) mrel) v1 v2.
Proof.
  revert v2.
  induction v1; intros; constructor; intro H; inv H; constructor; auto.
  - apply IHv1. auto.
  - apply IHv1. auto.
Qed.

Lemma initial_state_Cminor_equiv p s:
  Language.initial_state Language_ext_Cminor p s <-> Cminor.initial_state p s.
Proof.
  constructor; intro X.
  - destruct X as [a [f [m0 [Hm0 [Ha [Hf [Hsig ?]]]]]]]. simpl in *. subst.
    econstructor; eauto. rewrite <- Fundef_Cminor_funsig. auto.
  - inv X. repeat eexists; eauto.
    rewrite Fundef_Cminor_funsig. auto.
Qed.

Lemma initial_state_CminorSel_equiv p s:
  Language.initial_state Language_ext_CminorSel p s <-> CminorSel.initial_state p s.
Proof.
  constructor; intro X.
  - destruct X as [a [f [m0 [Hm0 [Ha [Hf [Hsig ?]]]]]]]. simpl in *. subst.
    econstructor; eauto. rewrite <- Fundef_CminorSel_funsig. auto.
  - inv X. repeat eexists; eauto.
    rewrite Fundef_CminorSel_funsig. auto.
Qed.

Lemma final_state_Cminor_equiv p r:
  Language.final_state Language_ext_Cminor p r <-> Cminor.final_state p r.
Proof.
  constructor; intro X; inv X; simpl in *; econstructor; simpl; eauto.
Qed.

Lemma final_state_CminorSel_equiv p r:
  Language.final_state Language_ext_CminorSel p r <-> CminorSel.final_state p r.
Proof.
  constructor; intro X; inv X; simpl in *; econstructor; simpl; eauto.
Qed.

Program Definition mrelT_props:
  @mrelT_propsT Language_ext_Cminor Language_ext_CminorSel
                transf_sigT transf_efT transf_vT _ mrelT_ops :=
  mkmrelT_propsT _ _ _ _ _ _ _.
Next Obligation. repeat constructor. Qed.
Next Obligation. repeat constructor. Qed.
Next Obligation. inv H. auto. Qed.
Next Obligation.
  apply initial_state_Cminor_equiv in H1. apply initial_state_CminorSel_equiv in H2.
  exploit sel_initial_states; eauto. intros [s2' [Hs2' Hinit]].
  cut (s2 = s2').
  { intro. subst. exists tt. eexists. econstructor; eauto. }
  inv H2. inv Hs2'. unfold ge, ge0 in *.
  rewrite H in H2. inv H2. rewrite H0 in H5. inv H5. rewrite H3 in H6. inv H6.
  auto.
Qed.
Next Obligation.
  apply (mrelT_ops_lessdef_list mrel args1 args2) in Hargs.
  destruct fd1; inv Hfd1. destruct fd2; inv Hfd2.
  inv Hs0. inv Hmrel. destruct MS as [MS|MS]; inv MS.

  (* external call *)
  exploit external_call_mem_extends; eauto.
  intros [vres' [m2' [A [B [C D]]]]].
  eexists. eexists. eexists. eexists. eexists. exists tt. eexists.
  repeat (split; [eauto; fail|]).
  cut (step (Genv.globalenv p2) (Callstate (External ef2) args2 es2 m2) evt (Returnstate vres' es2 m2')).
  { intro S. split; eauto. split; auto. econstructor; eauto.
    left. econstructor; eauto.
  }
  constructor.
  eapply external_call_symbols_preserved; eauto.
  apply symbols_preserved. auto. apply varinfo_preserved. auto.
Qed.

Section STATE_LSIM.
  
Variable (fprog:Cminor.program).
Variable (ftprog:CminorSel.program).
Hypothesis (Hfsim: @program_weak_lsim Language_Cminor Language_CminorSel transf_sigT transf_efT transf_vT
                                      fprog ftprog).

Hypothesis (Hfprog: program_linkeq Language_Cminor prog fprog).
Hypothesis (Hftprog: program_linkeq Language_CminorSel tprog ftprog).

Lemma match_states_state_lsim es es' eF F s1 s1'
      (MS: match_states fprog ftprog s1 s1'):
  @state_lsim Language_ext_Cminor Language_ext_CminorSel transf_sigT _
              mrelT_ops fprog ftprog es es' eF F (WF.from_nat (measure s1)) s1 s1'.
Proof.
  revert F s1 s1' MS. pcofix CIH. intros F s1 s1' MS. pfold.
  destruct (classic (exists r, Cminor.final_state s1 r)).
  { subst. destruct H as [rval Hrval]. eapply _state_lsim_term; eauto.
    - apply final_state_Cminor_equiv. eauto.
    - apply final_state_CminorSel_equiv. eapply sel_final_states; eauto.
  }
  subst. constructor; auto.
  { repeat intro. apply H. exists r0. apply final_state_Cminor_equiv. auto. }
  intros. exploit sel_step_correct; eauto. simpl.
  intros [[s2' [Hs2' Hmatch2]]|[Hmeasure [Hevt Hmatch2]]].
  { eexists. exists s2'. exists tt.
    split; [left; apply plus_one; auto|].
    split; [auto|].
    split; [constructor; eauto|].
    destruct Hmatch2 as [Hmatch2|Hmatch2].
    - apply _state_lsim_or_csim_lsim. right. apply CIH. auto.
    - inversion Hmatch2. subst. eapply _state_lsim_or_csim_csim; simpl; eauto.
      + apply (mrelT_ops_lessdef_list tt). auto.
      + constructor; auto.
      + intros. subst. inversion Hst2_mem. subst. destruct MS0 as [MS0|MS0]; inv MS0.
        right. apply CIH. constructor; auto.
  }
  { subst. eexists. eexists. exists tt.
    split; [right; split; eauto; [apply star_refl|]; constructor; eauto|].
    split; [auto|].
    split; [constructor; eauto|].
    destruct Hmatch2 as [Hmatch2|Hmatch2].
    - apply _state_lsim_or_csim_lsim. right. apply CIH. auto.
    - inversion Hmatch2. subst. eapply _state_lsim_or_csim_csim; simpl; eauto.
      + apply (mrelT_ops_lessdef_list tt). auto.
      + constructor; auto.
      + intros. subst. inversion Hst2_mem. subst. destruct MS0 as [MS0|MS0]; inv MS0.
        right. apply CIH. constructor; auto.
  }
Qed.

Lemma sel_function_lsim
      f tf (Hf: sel_function hf (Genv.globalenv prog) f = OK tf):
  @function_lsim Language_ext_Cminor Language_ext_CminorSel transf_sigT _
                 mrelT_ops fprog ftprog f tf.
Proof.
  constructor. intros. pfold. constructor; subst; auto.
  { intros ? Hfinal. apply final_state_Cminor_equiv in Hfinal. inv Hfinal. }
  intros. destruct fd_src; inv Hfd_src. destruct fd_tgt; inv Hfd_tgt. inversion Hst2_src. subst.
  inv Hmrel_entry. destruct MS as [MS|MS]; inversion MS; subst.

  (* internal function *)
  unfold sel_function in Hf. monadInv Hf.
  exploit Mem.alloc_extends. eauto. eauto. apply Zle_refl. apply Zle_refl.
  intros [m2' [A B]].
  eexists. eexists. exists tt. split.
  left. apply plus_one. simpl. constructor; eauto.
  simpl. split; [auto|].
  cut (match_states fprog ftprog
                    (Cminor.State f (Cminor.fn_body f) es_src (Vptr sp Int.zero)
                                  (set_locals (Cminor.fn_vars f)
                                              (set_params args_src (Cminor.fn_params f))) m')
                    (State
                       {|
                         fn_sig := Cminor.fn_sig f;
                         fn_params := Cminor.fn_params f;
                         fn_vars := Cminor.fn_vars f;
                         fn_stackspace := Cminor.fn_stackspace f;
                         fn_body := x |} x es_tgt (Vptr sp Int.zero)
                       (set_locals (Cminor.fn_vars f)
                                   (set_params args_tgt (Cminor.fn_params f))) m2')).
  { intro MS2. split; [constructor; eauto|].
    constructor. left. apply match_states_state_lsim. auto.
  }
  econstructor; try apply EQ; eauto.
  unfold sel_function. unfold Cminor.fundef in *. simpl in *. rewrite EQ. auto.
  apply set_locals_lessdef. apply set_params_lessdef. auto.
Qed.

End STATE_LSIM.

Lemma Selection_program_lsim_aux:
  @program_lsim Language_Cminor Language_CminorSel transf_sigT transf_efT transf_vT
                (@function_lsim Language_ext_Cminor Language_ext_CminorSel transf_sigT _ mrelT_ops)
                prog tprog.
Proof.
  generalize sel_function_lsim.
  destruct prog as [defs main]. simpl in *.
  unfold transform_partial_program, transform_partial_program2 in TRANSFPROG.
  monadInv TRANSFPROG. rename x into tdefs.
  simpl in *. intro Hlsim. constructor; simpl; auto.
  revert Hlsim EQ.
  generalize tdefs at 2 as ftdefs.
  generalize defs at 1 2 3 5 as fdefs.
  revert defs tdefs.
  induction defs; simpl; intros tdefs fdefs ftdefs Hlsim Hglobdefs; inv Hglobdefs; try constructor.
  destruct a. destruct g.
  - match goal with
      | [H: match ?tf with | OK _ => _ | Error _ => _ end = _ |- _] => destruct tf eqn:Htf; inv H
    end.
    monadInv H1. constructor; simpl in *; try apply IHdefs; auto.
    split; auto. apply (@globdef_lsim_fun Language_Cminor Language_CminorSel).
    destruct f; simpl in *.
    + monadInv Htf. constructor; simpl; intros.
      monadInv EQ0. split; auto. repeat intro.
      apply Hlsim; auto. unfold sel_function. rewrite EQ1. auto.
    + inv Htf.
      eapply globfun_lsim_intro; eauto; simpl; auto.
  - monadInv H0. constructor; simpl in *; try apply IHdefs; auto.
    split; auto. apply (@globdef_lsim_var Language_Cminor Language_CminorSel).
    repeat constructor.
Qed.

End PRESERVATION.

Lemma Selection_program_lsim prog tprog (Hprog: sel_program prog = OK tprog):
  @program_lsim Language_Cminor Language_CminorSel transf_sigT transf_efT transf_vT
                (@function_lsim Language_ext_Cminor Language_ext_CminorSel transf_sigT _ mrelT_ops)
                prog tprog.
Proof.
  apply Selection_program_lsim_aux.
  monadInv Hprog. rewrite Hget_helpers in EQ. inv EQ. auto.
Qed.
