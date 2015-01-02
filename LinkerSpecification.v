Require Import RelationClasses.
Require String.
Require Import Coqlib Coqlib_linker.
Require Import Maps Maps_linker.
Require Import Integers Floats Values AST Globalenvs.
Require Import Errors Behaviors Compiler Smallstep.

Set Implicit Arguments.

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

(** Structures *)

Structure Sig: Type := mkSig {
  Sig_carrier :> Type;
  Sig_dec: forall (sig1 sig2:Sig_carrier), {sig1 = sig2} + {sig1 <> sig2}
}.

Structure F (sigT:Sig): Type := mkF {
  F_carrier :> Type;
  F_sig: forall (f:F_carrier), sigT
}.

Structure EF (sigT:Sig): Type := mkEF {
  EF_carrier :> Type;
  EF_dec: forall (ef1 ef2:EF_carrier), {ef1 = ef2} + {ef1 <> ef2};
  EF_linkable: forall (ef:EF_carrier), bool;
  EF_sig: forall (ef:EF_carrier), sigT
}.

Structure Fundef (sigT:Sig) (fT:F sigT) (efT:EF sigT) := mkFundef {
  Fundef_carrier :> Type;
  Fundef_dec: forall (fd:Fundef_carrier), fT + efT;
  Fundef_sig :=
    fun fd =>
      match Fundef_dec fd with
        | inl f => fT.(F_sig) f
        | inr ef => efT.(EF_sig) ef
      end
}.

Structure V: Type := mkV {
  V_carrier :> Type;
  V_dec: forall (v1 v2:V_carrier), {v1 = v2} + {v1 <> v2}
}.

Structure Language: Type := mkLanguage {
  sigT: Sig;
  fT: F sigT;
  efT: EF sigT;
  fundefT: Fundef fT efT;
  vT: V;

  globdefT := AST.globdef fundefT vT;
  progT := AST.program fundefT vT
}.

(** Canonical Structures *)

Canonical Structure Sig_type: Sig := mkSig Ctypes.type_eq.
Canonical Structure Sig_signature: Sig := mkSig signature_eq.

Canonical Structure F_C: F Sig_type := mkF Sig_type Csyntax.type_of_function.
Canonical Structure F_Clight: F Sig_type := mkF Sig_type Clight.type_of_function.
Canonical Structure F_Csharpminor: F Sig_signature := mkF Sig_signature Csharpminor.fn_sig.
Canonical Structure F_Cminor: F Sig_signature := mkF Sig_signature Cminor.fn_sig.
Canonical Structure F_CminorSel: F Sig_signature := mkF Sig_signature CminorSel.fn_sig.
Canonical Structure F_RTL: F Sig_signature := mkF Sig_signature RTL.fn_sig.
Canonical Structure F_LTL: F Sig_signature := mkF Sig_signature LTL.fn_sig.
Canonical Structure F_Linear: F Sig_signature := mkF Sig_signature Linear.fn_sig.
Canonical Structure F_Mach: F Sig_signature := mkF Sig_signature Mach.fn_sig.
Canonical Structure F_Asm: F Sig_signature := mkF Sig_signature Asm.fn_sig.

Canonical Structure EF_external_function_ext: EF Sig_type :=
  mkEF Sig_type
       external_function_ext_eq
       (fun ef => match ef with (EF_external _ _, _, _, _) => true | _ => false end)
       (fun ef => match ef with (_, targs, tres, cc) => Ctypes.Tfunction targs tres cc end).
Canonical Structure EF_external_function: EF Sig_signature :=
  mkEF Sig_signature
       external_function_eq
       (fun ef => match ef with EF_external _ _ => true | _ => false end)
       ef_sig.

Canonical Structure Fundef_C: Fundef F_C EF_external_function_ext :=
  mkFundef F_C EF_external_function_ext
           (fun fd =>
              match fd with
                | Csyntax.Internal f => inl f
                | Csyntax.External ef targs tres cc => inr (ef, targs, tres, cc)
              end).
Canonical Structure Fundef_Clight: Fundef F_Clight EF_external_function_ext :=
  mkFundef F_Clight EF_external_function_ext
           (fun fd =>
              match fd with
                | Clight.Internal f => inl f
                | Clight.External ef targs tres cc => inr (ef, targs, tres, cc)
              end).
Canonical Structure Fundef_common (fT:F Sig_signature): Fundef fT EF_external_function :=
  mkFundef fT EF_external_function
           (fun fd =>
              match fd with
                | AST.Internal f => inl f
                | AST.External ef => inr ef
              end).

Canonical Structure V_type: V := mkV Ctypes.type_eq.
Canonical Structure V_unit: V := mkV unit_eq.

Canonical Structure Language_C: Language := mkLanguage Fundef_C V_type.
Canonical Structure Language_Clight: Language := mkLanguage Fundef_Clight V_type.
Canonical Structure Language_Csharpminor: Language := mkLanguage (Fundef_common F_Csharpminor) V_unit.
Canonical Structure Language_Cminor: Language := mkLanguage (Fundef_common F_Cminor) V_unit.
Canonical Structure Language_CminorSel: Language := mkLanguage (Fundef_common F_CminorSel) V_unit.
Canonical Structure Language_RTL: Language := mkLanguage (Fundef_common F_RTL) V_unit.
Canonical Structure Language_LTL: Language := mkLanguage (Fundef_common F_LTL) V_unit.
Canonical Structure Language_Linear: Language := mkLanguage (Fundef_common F_Linear) V_unit.
Canonical Structure Language_Mach: Language := mkLanguage (Fundef_common F_Mach) V_unit.
Canonical Structure Language_Asm: Language := mkLanguage (Fundef_common F_Asm) V_unit.

(** Linker definition *)
Section LINKER.

Variable (lang:Language).
  
Let sigT := lang.(sigT).
Let fT := lang.(fT).
Let efT := lang.(efT).
Let fundefT := lang.(fundefT).
Let vT := lang.(vT).

Let f_sig := fT.(F_sig).
Let ef_sig := efT.(EF_sig).
Let ef_dec := efT.(EF_dec).
Let fundef_dec := fundefT.(Fundef_dec).
Let v_dec := vT.(V_dec).

Ltac clarify :=
  repeat
    (try match goal with
           | [H1: fundef_dec ?f = _, H2: fundef_dec ?f = _ |- _] =>
             rewrite H1 in H2; inv H2
         end;
     auto).

(** `linkable a b` means we can remove `a` and take `b` when the two are linked. *)

Inductive globfun_linkable (f1 f2:fundefT): Prop :=
| globfun_linkable_ei (* TODO: type check? *)
    e1 i2 (H1: fundef_dec f1 = inr e1) (H2: fundef_dec f2 = inl i2)
    (Hsig: ef_sig e1 = f_sig i2)
| globfun_linkable_ee
    e (H1: fundef_dec f1 = inr e) (H1: fundef_dec f2 = inr e)
.

Inductive globvar_linkable (v1 v2:globvar vT): Prop :=
| globvar_linkable_intro
    (Hinfo: v1.(gvar_info) = v2.(gvar_info))
    (Hinit: v1.(gvar_init) = nil)
    (Hreadonly: v1.(gvar_readonly) = v2.(gvar_readonly))
    (Hvolatile: v1.(gvar_volatile) = v2.(gvar_volatile))
.

Inductive globdef_linkable: forall (g1 g2:globdef fundefT vT), Prop :=
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
  - destruct (sigT.(Sig_dec) (ef_sig e1) (f_sig i2)).
    + left. econstructor; eauto.
    + right. contradict n. inv n; clarify.
  - destruct (ef_dec e1 e2); [subst|].
    + left. eapply globfun_linkable_ee; eauto.
    + right. contradict n. inv n; clarify.
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

Definition globvar_linkable_dec (v1 v2:globvar vT): {globvar_linkable v1 v2} + {~ globvar_linkable v1 v2}.
Proof.
  destruct v1 as [info1 init1 readonly1 volatile1].
  destruct v2 as [info2 init2 readonly2 volatile2].
  destruct (bool_dec readonly1 readonly2); [subst|].
  { destruct (bool_dec volatile1 volatile2); [subst|].
    { destruct (v_dec info1 info2); [subst|].
      { destruct (list_eq_dec init_data_dec init1 nil).
        { left. constructor; simpl in *; auto. }
        { right. intro X. inv X. simpl in *.
          destruct Hinit; auto.
        }
      }
      { right. contradict n. inv n. simpl in *.
        destruct (v_dec info1 info2); auto.
      }
    }
    { right. contradict n. inv n. auto. }
  }
  { right. contradict n. inv n. auto. }
Defined.

Definition globdef_linkable_dec (g1 g2:globdef fundefT vT): {globdef_linkable g1 g2} + {~ globdef_linkable g1 g2}.
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

Definition link_globdefs (defs1 defs2:PTree.t (globdef fundefT vT)): option (PTree.t (globdef fundefT vT)) :=
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
  then Some (PTree_option_map (fun _ x => x) defs)
  else None.

Definition link_globdef_list (defs1 defs2:list (positive * globdef fundefT vT)): option (list (positive * globdef fundefT vT)) :=
  match link_globdefs (PTree_unelements defs1) (PTree_unelements defs2) with
    | Some defs => Some (PTree.elements defs)
    | None => None
  end.

Definition link_program (prog1 prog2:program fundefT vT): option (program fundefT vT) :=
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
          cprog (Hcprog: Some cprog = link_program Language_C cprog1 cprog2)
          asmprog (Hasmprog: Some asmprog = link_program Language_Asm asmprog1 asmprog2):
    separately_compiled cprog asmprog
.

Definition separate_compilation_correctness :=
  forall
    cprog asmprog asmbeh
    (Hsepcomp: separately_compiled cprog asmprog)
    (Hbeh: program_behaves (Asm.semantics asmprog) asmbeh),
  exists cbeh,
    program_behaves (Csem.semantics cprog) cbeh /\ behavior_improves cbeh asmbeh.
