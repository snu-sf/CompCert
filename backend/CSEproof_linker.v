Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Errors.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Op.
Require Import Registers.
Require Import RTL.
Require Import Kildall.
Require Import ValueDomain.
Require Import ValueAOp.
Require Import ValueAnalysis.
Require Import CSEdomain.
Require Import CombineOp.
Require Import CombineOpproof.
Require Import CSE.
Require Import CSEproof.
Require Import LinkerSpecification.
Require Import Linkeq ProgramSim.

Section PRESERVATION.

Let transf_EF (ef:external_function) := OK ef.
Let transf_V (v_src:unit) := OK v_src.
Let fundef_dec := (@common_fundef_dec function).

Variable fprog: program.
Variable ftprog: program.
Hypothesis (Hweak_sim:
              program_weak_sim
                fundef_dec fundef_dec transf_EF transf_V
                fprog ftprog).

Let globfun_weak_sim :=
  globfun_sim fundef_dec fundef_dec transf_EF (fun _ _ _ _ => True) fprog ftprog.

Let ge := Genv.globalenv fprog.
Let tge := Genv.globalenv ftprog.

Lemma find_function_translated:
  forall ros rs fd rs',
  find_function ge ros rs = Some fd ->
  regs_lessdef rs rs' ->
  exists tfd, find_function tge ros rs' = Some tfd /\ globfun_weak_sim fd tfd.
Proof.
  unfold find_function; intros; destruct ros.
- specialize (H0 r). inv H0.
  eapply find_funct_match; eauto.
  rewrite <- H2 in H; discriminate.
- unfold ge, tge in *. erewrite find_symbol_match; eauto.
  destruct (Genv.find_symbol (Genv.globalenv fprog) i).
  eapply find_funct_ptr_match; eauto.
  discriminate.
Qed.

Variable prog: program.
Variable tprog: program.
Hypothesis TRANSF: transf_program prog = OK tprog.
Hypothesis (Hfprog: program_linkeq (@common_fundef_dec function) prog fprog).
Hypothesis (Hftprog: program_linkeq (@common_fundef_dec function) tprog ftprog).
Let rm := romem_for_program prog.

Inductive match_local: state -> state -> Prop :=
  | match_states_intro:
      forall s sp pc rs m s' rs' m' f approx
             (ANALYZE: analyze f (vanalyze rm f) = Some approx)
             (SAT: exists valu, numbering_holds valu ge sp rs m approx!!pc)
             (RLD: regs_lessdef rs rs')
             (MEXT: Mem.extends m m'),
      match_local (State s f sp pc rs m)
                  (State s' (transf_function' f approx) sp pc rs' m')
  | match_states_call:
      forall s f tf args m s' args' m',
      transf_fundef rm f = OK tf ->
      Val.lessdef_list args args' ->
      Mem.extends m m' ->
      match_local (Callstate s f args m)
                  (Callstate s' tf args' m')
  | match_states_return:
      forall s s' v v' m m',
      Val.lessdef v v' ->
      Mem.extends m m' ->
      match_local (Returnstate s v m)
                  (Returnstate s' v' m').

(** The proof of simulation is a case analysis over the transition
  in the source code. TODO *)

End PRESERVATION.
