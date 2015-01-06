Require Import RelationClasses.
Require Import Coqlib.
Require Import paco.
Require Import WFType.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Events.
Require Import Memory.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Language.
Require Import Op.
Require Import Registers.
Require Import Language Linker ProgramLSim.
Require Import RTL.

Set Implicit Arguments.

(* common definitions/lemmas on RTL *)

Definition transf_sigT := fun (sig:signature) => sig.
Definition transf_efT := fun (ef:external_function) => Errors.OK ef.
Definition transf_vT := fun (tt:unit) => Errors.OK tt.
Lemma transf_efT_sigT:
  forall (ef_src : efT Language_RTL) (ef_tgt : efT Language_RTL),
    Errors.OK ef_src = Errors.OK ef_tgt ->
    transf_sigT (EF_sig (efT Language_RTL) ef_src) =
    EF_sig (efT Language_RTL) ef_tgt.
Proof. intros. inv H. auto. Qed.
Lemma transf_efT_linkable:
  forall (ef_src : efT Language_RTL) (ef_tgt : efT Language_RTL),
    Errors.OK ef_src = Errors.OK ef_tgt ->
    (EF_linkable (efT Language_RTL) ef_src) = (EF_linkable (efT Language_RTL) ef_tgt).
Proof. intros. inv H. auto. Qed.
Hint Resolve transf_efT_sigT transf_efT_linkable.

Section FUTURE.

Variable (fprog ftprog:program).
Hypothesis (Hfsim: @program_weak_lsim Language_RTL Language_RTL transf_sigT transf_efT transf_vT
                                      fprog ftprog).

Let ge := Genv.globalenv fprog.
Let tge := Genv.globalenv ftprog.

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof (symbols_preserved Hfsim).

Lemma varinfo_preserved:
  forall b, Genv.find_var_info tge b = Genv.find_var_info ge b.
Proof.
  intros. exploit varinfo_preserved; try exact transf_efT_sigT; try exact Hfsim.
  instantiate (1 := b). unfold ge, tge, fundef. simpl in *.
  match goal with
    | [|- context[match ?v1 with | Some _ => match ?v2 with | Some _ => _ | None => _ end | None => _ end]] =>
      destruct v1, v2; intros; auto; inv H
  end.
  destruct g0; auto.
Qed.

Lemma funct_ptr_translated:
  forall (b: block) (f: RTL.fundef),
  Genv.find_funct_ptr ge b = Some f ->
  exists tf, Genv.find_funct_ptr tge b = Some tf /\
             globfun_weak_lsim Language_RTL Language_RTL transf_sigT transf_efT ge tge f tf.
Proof (funct_ptr_translated Hfsim).

Lemma functions_translated:
  forall (v: val) (f: RTL.fundef),
  Genv.find_funct ge v = Some f ->
  exists tf, Genv.find_funct tge v = Some tf /\
             globfun_weak_lsim Language_RTL Language_RTL transf_sigT transf_efT ge tge f tf.
Proof (functions_translated Hfsim).

Lemma find_function_translated_Renumber:
  forall ros rs fd,
  find_function ge ros rs = Some fd ->
  exists tfd, find_function tge ros rs = Some tfd /\
              globfun_weak_lsim Language_RTL Language_RTL transf_sigT transf_efT ge tge fd tfd.
Proof.
  unfold find_function; intros; destruct ros.
- apply functions_translated; auto.
- rewrite symbols_preserved. destruct (Genv.find_symbol ge i).
  apply funct_ptr_translated; auto.
  discriminate.
Qed.

Lemma find_function_translated_CSE:
  forall ros rs fd rs',
  find_function ge ros rs = Some fd ->
  CSEproof.regs_lessdef rs rs' ->
  exists tfd, find_function tge ros rs' = Some tfd /\
              globfun_weak_lsim Language_RTL Language_RTL transf_sigT transf_efT ge tge fd tfd.
Proof.
  unfold find_function; intros; destruct ros.
- specialize (H0 r). inv H0.
  apply functions_translated; auto.
  rewrite <- H2 in H; discriminate.
- rewrite symbols_preserved. destruct (Genv.find_symbol ge i).
  apply funct_ptr_translated; auto.
  discriminate.
Qed.

Lemma find_function_translated_Tailcall:
  forall ros rs fd rs',
  find_function ge ros rs = Some fd ->
  Tailcallproof.regset_lessdef rs rs' ->
  exists tfd, find_function tge ros rs' = Some tfd /\
              globfun_weak_lsim Language_RTL Language_RTL transf_sigT transf_efT ge tge fd tfd.
Proof.
  unfold find_function; intros; destruct ros.
- specialize (H0 r). inv H0.
  apply functions_translated; auto.
  rewrite <- H2 in H; discriminate.
- rewrite symbols_preserved. destruct (Genv.find_symbol ge i).
  apply funct_ptr_translated; auto.
  discriminate.
Qed.

Lemma find_function_translated_Constprop:
  forall ros rs fd rs',
  find_function ge ros rs = Some fd ->
  Constpropproof.regs_lessdef rs rs' ->
  exists tfd, find_function tge ros rs' = Some tfd /\
              globfun_weak_lsim Language_RTL Language_RTL transf_sigT transf_efT ge tge fd tfd.
Proof.
  unfold find_function; intros; destruct ros.
- specialize (H0 r). inv H0.
  apply functions_translated; auto.
  rewrite <- H2 in H; discriminate.
- rewrite symbols_preserved. destruct (Genv.find_symbol ge i).
  apply funct_ptr_translated; auto.
  discriminate.
Qed.

Lemma sig_preserved:
  forall f tf,
    globfun_weak_lsim Language_RTL Language_RTL transf_sigT transf_efT ge tge f tf ->
    funsig tf = funsig f.
Proof.
  intros. exploit sig_preserved; try exact transf_efT_sigT; eauto.
  unfold transf_sigT. rewrite ? Fundef_RTL_funsig. auto.
Qed.

End FUTURE.
