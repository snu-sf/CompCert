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
Require Import Tree.
Require Import sflib.

(** Pretty-printers (defined in Caml). *)
Parameter print_Clight: Clight.program -> unit.
Parameter print_Cminor: Cminor.program -> unit.
Parameter print_RTL: Z -> RTL.program -> unit.
Parameter print_LTL: LTL.program -> unit.
Parameter print_Mach: Mach.program -> unit.

Open Local Scope string_scope.

(** * Composing the translation passes *)

(** We first define useful monadic composition operators,
    along with funny (but convenient) notations. *)

Definition apply_total (A B: Type) (x: res A) (f: A -> B) : res B :=
  match x with Error msg => Error msg | OK x1 => OK (f x1) end.

Definition apply_partial (A B: Type)
                         (x: res A) (f: A -> res B) : res B :=
  match x with Error msg => Error msg | OK x1 => f x1 end.

Notation "a @@@ b" :=
   (apply_partial _ _ a b) (at level 50, left associativity).
Notation "a @@ b" :=
   (apply_total _ _ a b) (at level 50, left associativity).

Definition print {A: Type} (printer: A -> unit) (prog: A) : A :=
  let unused := printer prog in prog.

Definition time {A B: Type} (name: string) (f: A -> B) : A -> B := f.

(** Force [Initializers] and [Cexec] to be extracted as well. *)

Definition transl_init := Initializers.transl_init.
Definition cexec_do_step := Cexec.do_step.

(** The following lemmas help reason over compositions of passes. *)

Lemma print_identity:
  forall (A: Type) (printer: A -> unit) (prog: A),
  print printer prog = prog.
Proof.
  intros; unfold print. destruct (printer prog); auto. 
Qed.

Lemma compose_print_identity:
  forall (A: Type) (x: res A) (f: A -> unit), 
  x @@ print f = x.
Proof.
  intros. destruct x; simpl. rewrite print_identity. auto. auto. 
Qed.

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

(*Definition optimize_rtl_program := rtc optimize_rtl_program_1.*)

(*  Relation_Operators.clos_refl_trans  RTL.program optimize_rtl_program_1. *)

Definition rtl_opt_tree := Tree.tree_change_one optimize_rtl_program.

(* Inductive rtl_opt_tree: forall (tr: Tree.t RTL.program) (tr': Tree.t RTL.program), Prop := *)
(* | rtl_opt1_tree_base: forall r r' (ROPT: optimize_rtl_program r r'), *)
(*                         rtl_opt_tree (Tree.Tree_singleton r) (Tree.Tree_singleton r') *)
(* | rtl_opt1_tree_comp_left: forall r r' tr (ROPTT: rtl_opt_tree r r'), *)
(*                              rtl_opt_tree (Tree.Tree_composite r tr) (Tree.Tree_composite r' tr) *)
(* | rtl_opt1_tree_comp_right: forall r r' tr (ROPTT: rtl_opt_tree r r'), *)
(*                               rtl_opt_tree (Tree.Tree_composite tr r) (Tree.Tree_composite tr r'). *)

Definition compile_c_program (c: Csyntax.program) (a:Asm.program) : Prop :=
  exists rtl ortl,
    transf_c_program_to_rtl c = OK rtl
    /\ (rtc optimize_rtl_program) rtl ortl
    /\ transf_rtl_program_to_asm ortl = OK a.
