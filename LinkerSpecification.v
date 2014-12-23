Require Import RelationClasses.
Require String.
Require Import Coqlib Coqlib_linker.
Require Import Maps_linker.
Require Import Integers Floats Values AST Globalenvs.
Require Import Errors Behaviors Compiler Smallstep.

Set Implicit Arguments.


(* extended external function for C and Clight *)

Definition external_function_ext :=
  (external_function * Ctypes.typelist * Ctypes.type * calling_convention)%type.

Definition external_function_ext_eq (ef1 ef2: external_function_ext): {ef1 = ef2} + {ef1 <> ef2}.
Proof.
  destruct ef1 as [[[ef1 args1] res1] cc1].
  destruct ef2 as [[[ef2 args2] res2] cc2].
  decide equality.
  { destruct b, c.
    destruct (bool_dec cc_vararg cc_vararg0); [subst|].
    { destruct (bool_dec cc_structret cc_structret0); [subst|].
      { left. auto. }
      { right. contradict n. inv n. auto. }
    }
    { right. contradict n. inv n. auto. }
  }
  decide equality.
  { apply Ctypes.type_eq. }
  decide equality.
  { apply Ctypes.typelist_eq. }
  { apply external_function_eq. }
Defined.


(* classify function definitions into internal and external functions  *)

Definition fundef_decT T F := T -> F + external_function.

Definition C_fundef_dec : fundef_decT Csyntax.fundef Csyntax.function :=
  fun fundef =>
    match fundef with
      | Csyntax.Internal i => inl i
      | Csyntax.External ef args res cc => inr ef
    end.

Definition Clight_fundef_dec : fundef_decT Clight.fundef Clight.function :=
  fun fundef =>
    match fundef with
      | Clight.Internal i => inl i
      | Clight.External ef args res cc => inr ef
    end.

Definition common_fundef_dec (F:Type) : fundef_decT (AST.fundef F) F :=
  fun fundef =>
    match fundef with
      | Internal i => inl i
      | External ef => inr ef
    end.


(** Linker definition *)
Section LINKER.

Variable (fundefT F V:Type).
Variable (fundef_dec: fundef_decT fundefT F).
Variable (V_dec: forall (v1 v2:V), {v1 = v2} + {v1 <> v2}).

(** `linkable a b` means we can remove `a` and take `b` when the two are linked. *)

Inductive globfun_linkable (f1 f2:fundefT): Prop :=
| globfun_linkable_ei (* TODO: type check? *)
    e1 i2 (H1: fundef_dec f1 = inr e1) (H2: fundef_dec f2 = inl i2)
| globfun_linkable_ee
    e (H1: fundef_dec f1 = inr e) (H1: fundef_dec f2 = inr e)
.

Inductive globvar_linkable (v1 v2:globvar V): Prop :=
| globvar_linkable_intro
    (Hinfo: v1.(gvar_info) = v2.(gvar_info))
    (Hinit: v1.(gvar_init) = nil)
    (Hreadonly: v1.(gvar_readonly) = v2.(gvar_readonly))
    (Hvolatile: v1.(gvar_volatile) = v2.(gvar_volatile))
.

Inductive globdef_linkable: forall (g1 g2:globdef fundefT V), Prop :=
| globdef_linkable_fun
    f1 f2 (Hv: globfun_linkable f1 f2):
    globdef_linkable (Gfun f1) (Gfun f2)
| globdef_linkable_var
    v1 v2 (Hv: globvar_linkable v1 v2):
    globdef_linkable (Gvar v1) (Gvar v2)
.


(** `linkable` decidabilities. *)

Definition globfun_linkable_dec (f1 f2:fundefT): {globfun_linkable f1 f2} + {~ globfun_linkable f1 f2}.
Proof.
  destruct (fundef_dec f1) as [i1|e1] eqn:Hf1.
  { right. intro X. inv X.
    - rewrite Hf1 in H1. inv H1.
    - rewrite Hf1 in H1. inv H1.
  }
  destruct (fundef_dec f2) as [i2|e2] eqn:Hf2.
  { left. econstructor; eauto. }
  { destruct (external_function_eq e1 e2); [subst|].
    { left. eapply globfun_linkable_ee; eauto. }
    { right. contradict n. inv n; auto.
      - rewrite Hf2 in H2. inv H2.
      - rewrite Hf1 in H1. inv H1.
        rewrite Hf2 in H0. inv H0.
        auto.
    }
  }
Defined.

Definition init_data_dec (v1 v2:init_data): {v1 = v2} + {v1 <> v2}.
Proof.
  decide equality;
  (try apply Int.eq_dec);
  (try apply Int64.eq_dec);
  (try apply Float.eq_dec);
  (try apply Float32.eq_dec);
  (try apply zeq);
  (try apply ident_eq).
Defined.

Definition globvar_linkable_dec (v1 v2:globvar V): {globvar_linkable v1 v2} + {~ globvar_linkable v1 v2}.
Proof.
  destruct v1 as [info1 init1 readonly1 volatile1].
  destruct v2 as [info2 init2 readonly2 volatile2].
  destruct (bool_dec readonly1 readonly2); [subst|].
  { destruct (bool_dec volatile1 volatile2); [subst|].
    { destruct (V_dec info1 info2); [subst|].
      { destruct (list_eq_dec init_data_dec init1 nil).
        { left. constructor; simpl in *; auto. }
        { right. intro X. inv X. simpl in *.
          destruct Hinit; auto.
        }
      }
      { right. contradict n. inv n. simpl in *.
        destruct (V_dec info1 info2); auto.
      }
    }
    { right. contradict n. inv n. auto. }
  }
  { right. contradict n. inv n. auto. }
Defined.

Definition globdef_linkable_dec (g1 g2:globdef fundefT V): {globdef_linkable g1 g2} + {~ globdef_linkable g1 g2}.
Proof.
  destruct g1 as [f1|v1], g2 as [f2|v2].
  { destruct (globfun_linkable_dec f1 f2).
    { left. constructor. auto. }
    { right. contradict n. inv n. auto. }
  }
  { right. intro X. inv X. }
  { right. intro X. inv X. }
  { destruct (globvar_linkable_dec v1 v2).
    { left. constructor. auto. }
    { right. contradict n. inv n. auto. }
  }
Defined.


(** main definition *)

Definition link_globdefs (defs1 defs2:PTree.t (globdef fundefT V)): option (PTree.t (globdef fundefT V)) :=
  let defs :=
    PTree.combine
      (fun odef1 odef2 =>
         match odef1, odef2 with
           | None, None => None
           | Some _, None => Some odef1
           | None, Some _ => Some odef2
           | Some def1, Some def2 =>
             if globdef_linkable_dec def1 def2
             then Some odef2
             else if globdef_linkable_dec def2 def1
                  then Some odef1
                  else Some None
         end)
      defs1
      defs2
  in
  let defs_valid :=
    PTree_Properties.for_all
      defs
      (fun _ x => match x with | None => false | Some _ => true end)
  in
  if defs_valid
  then Some (PTree.option_map (fun _ x => x) defs)
  else None.

Definition link_globdef_list (defs1 defs2:list (positive * globdef fundefT V)): option (list (positive * globdef fundefT V)) :=
  match link_globdefs (PTree.unelements defs1) (PTree.unelements defs2) with
    | Some defs => Some (PTree.elements defs)
    | None => None
  end.

Definition link_program (prog1 prog2:program fundefT V): option (program fundefT V) :=
  match
    Pos.eqb prog1.(prog_main) prog2.(prog_main),
    link_globdef_list prog1.(prog_defs) prog2.(prog_defs)
  with
    | true, Some defs => Some (mkprogram defs prog1.(prog_main))
    | _, _ => None
  end.
End LINKER.


(** linker correctness statement *)

Inductive separately_compiled: forall (cprog: Csyntax.program) (asmprog: Asm.program), Prop :=
| separately_compiled_base cprog asmprog (Htransf: transf_c_program cprog = OK asmprog):
    separately_compiled cprog asmprog
| separately_compiled_link cprog1 cprog2 asmprog1 asmprog2
          (H1: separately_compiled cprog1 asmprog1)
          (H2: separately_compiled cprog2 asmprog2)
          cprog (Hcprog: Some cprog = link_program C_fundef_dec Ctypes.type_eq cprog1 cprog2)
          asmprog (Hasmprog: Some asmprog = link_program (@common_fundef_dec Asm.function) unit_eq asmprog1 asmprog2):
    separately_compiled cprog asmprog
.

Definition separate_compilation_correctness :=
  forall
    cprog asmprog asmbeh
    (Hsepcomp: separately_compiled cprog asmprog)
    (Hbeh: program_behaves (Asm.semantics asmprog) asmbeh),
  exists cbeh,
    program_behaves (Csem.semantics cprog) cbeh /\ behavior_improves cbeh asmbeh.
