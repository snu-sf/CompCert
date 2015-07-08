(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** The whole compiler and its proof of semantic preservation *)

(** Libraries. *)
Require Import String.
Require Import Coqlib.
Require Import Errors.
Require Import AST.
Require Import Smallstep.
(** Languages (syntax and semantics). *)
Require Csyntax.
Require Csem.
Require Cstrategy.
Require Cexec.
Require Clight.
Require Csharpminor.
Require Cminor.
Require CminorSel.
Require RTL.
Require LTL.
Require Linear.
Require Mach.
Require Asm.
(** Translation passes. *)
Require Initializers.
Require SimplExpr.
Require SimplLocals.
Require Cshmgen.
Require Cminorgen.
Require Selection.
Require RTLgen.
Require Tailcall.
Require Inlining.
Require Renumber.
Require Constprop.
Require CSE.
Require Deadcode.
Require Allocation.
Require Tunneling.
Require Linearize.
Require CleanupLabels.
Require Stacking.
Require Asmgen.
(** Proofs of semantic preservation. *)
Require SimplExprproof.
Require SimplLocalsproof.
Require Cshmgenproof.
Require Cminorgenproof.
Require Selectionproof.
Require RTLgenproof.
Require Tailcallproof.
Require Inliningproof.
Require Renumberproof.
Require Constpropproof.
Require CSEproof.
Require Deadcodeproof.
Require Allocproof.
Require Tunnelingproof.
Require Linearizeproof.
Require CleanupLabelsproof.
Require Stackingproof.
Require Asmgenproof.
Require Import Compiler.
Require Import sflib.

Definition transf_cminor_program_to_rtl (p: Cminor.program) : res RTL.program :=
   OK p
   @@ print print_Cminor
  @@@ time "Instruction selection" Selection.sel_program
  @@@ time "RTL generation" RTLgen.transl_program.

Definition transf_clight_program_to_rtl (p: Clight.program) : res RTL.program :=
  OK p 
   @@ print print_Clight
  @@@ time "Simplification of locals" SimplLocals.transf_program
  @@@ time "C#minor generation" Cshmgen.transl_program
  @@@ time "Cminor generation" Cminorgen.transl_program
  @@@ transf_cminor_program_to_rtl.

Definition transf_c_program_to_rtl (p: Csyntax.program) : res RTL.program :=
  OK p 
  @@@ time "Clight generation" SimplExpr.transl_program
  @@@ transf_clight_program_to_rtl.

Definition transf_rtl_program_to_asm (f: RTL.program) : res Asm.program :=
   OK f
   @@ print (print_RTL 0)
   @@@ time "Register allocation" Allocation.transf_program
   @@ print print_LTL
   @@ time "Branch tunneling" Tunneling.tunnel_program
  @@@ Linearize.transf_program
   @@ time "Label cleanup" CleanupLabels.transf_program
  @@@ time "Mach generation" Stacking.transf_program
   @@ print print_Mach
  @@@ time "Asm generation" Asmgen.transf_program.

Inductive optimize_rtl_program: forall (rtl: RTL.program) (ortl: RTL.program), Prop:=
| rtlopt_tailcall: forall r1,
                     optimize_rtl_program r1 (Tailcall.transf_program r1)
| rtlopt_inlining: forall r1 r1' (TR_OK: Inlining.transf_program r1 = OK r1'),
                     optimize_rtl_program r1 r1'
| rtlopt_renumber: forall r1,
                     optimize_rtl_program r1 (Renumber.transf_program r1)
| rtlopt_constprop: forall r1,
                      optimize_rtl_program r1 (Constprop.transf_program r1)
| rtlopt_cse: forall r1 r1' (TR_OK: CSE.transf_program r1 = OK r1'),
                optimize_rtl_program r1 r1'
| rtlopt_deadcode: forall r1 r1' (TR_OK: Deadcode.transf_program r1 = OK r1'),
                     optimize_rtl_program r1 r1'.

Definition compile_c_program (c: Csyntax.program) (a:Asm.program) : Prop :=
  exists rtl ortl,
    transf_c_program_to_rtl c = OK rtl
    /\ (rtc optimize_rtl_program) rtl ortl
    /\ transf_rtl_program_to_asm ortl = OK a.

Ltac simplify:=
  match goal with
    | H: match ?x with
           | OK _ => _
           | Error _ => Error _
         end = OK _
      |- _ => (destruct x eqn:?D;[|inv H])
    | H: OK _ = OK _ |- _ => inv H
  end.

Lemma transf_c_program_compile_c_program:
  forall p tp
         (Htrans: transf_c_program p = OK tp),
    compile_c_program p tp.
Proof.
  intros.
  unfold transf_c_program in Htrans.
  unfold transf_clight_program in Htrans.
  unfold transf_cminor_program in Htrans.
  unfold Compiler.time, Compiler.print in Htrans.
  unfold Compiler.apply_partial, Compiler.apply_total in Htrans.

  unfold compile_c_program.
  unfold transf_c_program_to_rtl.
  unfold transf_clight_program_to_rtl.
  unfold transf_cminor_program_to_rtl.
  unfold time, print, apply_partial, apply_total.

  destruct (SimplExpr.transl_program p); [|inversion Htrans].
  destruct (SimplLocals.transf_program p0); [|inversion Htrans].
  destruct (Cshmgen.transl_program p1); [|inversion Htrans].
  destruct (Cminorgen.transl_program p2); [|inversion Htrans].
  destruct (Selection.sel_program p3); [|inversion Htrans].
  destruct (RTLgen.transl_program p4); [|inversion Htrans].
  exists p5. clear -Htrans.

  unfold transf_rtl_program in Htrans.
  unfold Compiler.time, Compiler.apply_partial, Compiler.apply_total, Compiler.print in Htrans.
  repeat simplify.

  unfold Compiler.total_if, Compiler.partial_if in *.
  eexists. split; auto.
  split.
  - assert (Hr1: rtc optimize_rtl_program p5 p17).
    { destruct (Compopts.optim_tailcalls tt).
      - econs 3; econs 1; [econs 1 | econs 2; eauto].
      - econs 1. econs 2. eauto.
    }
    assert (Hr2: rtc optimize_rtl_program p17 p9).
    { destruct (Compopts.optim_CSE tt).
      - destruct (Compopts.optim_constprop tt).
        + econs 3. econs 1. econs 3.
          econs 3. econs 1. econs 4.
          econs 3. econs 1. econs 3.
          econs 1. econs 5. eauto.
        + econs 3. econs 1. econs 3.
          econs 1. econs 5. eauto.
      - destruct (Compopts.optim_constprop tt).
        + econs 3. econs 1. econs 3.
          econs 3. econs 1. econs 4.
          econs 1. inv D9. econs 3.
        + econs 1. inv D9. econs 3.
    }
    assert (Hr3: rtc optimize_rtl_program p9 p7).
    { destruct (Compopts.optim_redundancy tt).
      - econs 1. econs 6. eauto.
      - inv D7. econs 2.
    }
    econs 3; econs 3; eauto.
  - clear -D0 D2 D5 Htrans.
    unfold transf_rtl_program_to_asm.
    unfold apply_partial, apply_total.
    unfold time, print.
    destruct (Allocation.transf_program p7); [|inv D5]. simplify.
    rewrite D2, D0. auto.
Qed.
