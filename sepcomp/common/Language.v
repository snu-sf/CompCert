Require Import RelationClasses.
Require String.
Require Import Coqlib Coqlib_sepcomp.
Require Import Maps Maps_sepcomp.
Require Import Integers Floats Values AST Globalenvs.
Require Import Errors Behaviors Compiler Smallstep.
Require Import Memory.

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

Structure EquivalentType (A B:Type) := mkEquivalentType {
  AtoB: forall (a:A), B;
  BtoA: forall (b:B), A;
  HABA: forall a, BtoA (AtoB a) = a;
  HBAB: forall b, AtoB (BtoA b) = b
}.

Lemma EquivalentType_AtoB_inj
      A B (E:EquivalentType A B)
      a1 a2 (H: E.(AtoB) a1 = E.(AtoB) a2):
  a1 = a2.
Proof.
  rewrite <- (HABA E a1), <- (HABA E a2).
  rewrite H. auto.
Qed.

Lemma EquivalentType_AtoB_sur
      A B (E:EquivalentType A B)
      b:
  exists a, E.(AtoB) a = b.
Proof. exists (E.(BtoA) b). apply HBAB. Qed.

Lemma EquivalentType_BtoA_inj
      A B (E:EquivalentType A B)
      b1 b2 (H: E.(BtoA) b1 = E.(BtoA) b2):
  b1 = b2.
Proof.
  rewrite <- (HBAB E b1), <- (HBAB E b2).
  rewrite H. auto.
Qed.

Lemma EquivalentType_BtoA_sur
      A B (E:EquivalentType A B)
      a:
  exists b, E.(BtoA) b = a.
Proof. exists (E.(AtoB) a). apply HABA. Qed.

Structure Fundef (sigT:Sig) (fT:F sigT) (efT:EF sigT) := mkFundef {
  Fundef_carrier :> Type;
  Fundef_equiv :> EquivalentType Fundef_carrier (fT + efT);
  Fundef_sig :=
    fun fd =>
      match Fundef_equiv.(AtoB) fd with
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

Program Canonical Structure Fundef_C: Fundef F_C EF_external_function_ext :=
  @mkFundef _ F_C EF_external_function_ext Csyntax.fundef
            (mkEquivalentType
               (fun fd =>
                  match fd with
                    | Csyntax.Internal f => inl f
                    | Csyntax.External ef targs tres cc => inr (ef, targs, tres, cc)
                  end)
               (fun fd =>
                  match fd with
                    | inl f => Csyntax.Internal f
                    | inr (ef, targs, tres, cc) => Csyntax.External ef targs tres cc
                  end)
               _ _).
Next Obligation. destruct a; auto. Qed.
Next Obligation. destruct b; auto. destruct e. destruct p. destruct p. auto. Qed.
Program Canonical Structure Fundef_Clight: Fundef F_Clight EF_external_function_ext :=
  @mkFundef _ F_Clight EF_external_function_ext Clight.fundef
            (mkEquivalentType
               (fun fd =>
                  match fd with
                    | Clight.Internal f => inl f
                    | Clight.External ef targs tres cc => inr (ef, targs, tres, cc)
                  end)
               (fun fd =>
                  match fd with
                    | inl f => Clight.Internal f
                    | inr (ef, targs, tres, cc) => Clight.External ef targs tres cc
                  end)
               _ _).
Next Obligation. destruct a; auto. Qed.
Next Obligation. destruct b; auto. destruct e. destruct p. destruct p. auto. Qed.
Program Canonical Structure Fundef_common (fT:F Sig_signature): Fundef fT EF_external_function :=
  @mkFundef _ fT EF_external_function (AST.fundef fT)
            (mkEquivalentType
               (fun fd =>
                  match fd with
                    | AST.Internal f => inl f
                    | AST.External ef => inr ef
                  end)
               (fun fd =>
                  match fd with
                    | inl f => AST.Internal f
                    | inr ef => AST.External ef
                  end)
               _ _).
Next Obligation. destruct a; auto. Qed.
Next Obligation. destruct b; auto. Qed.

Canonical Structure V_type: V := mkV Ctypes.type_eq.
Canonical Structure V_unit: V := mkV unit_eq.

Canonical Structure Language_C: Language := mkLanguage Fundef_C V_type.

Lemma Fundef_C_type_of_fundef f: Fundef_sig Fundef_C f = Csyntax.type_of_fundef f.
Proof. unfold Fundef_sig. destruct f; auto. Qed.

Canonical Structure Language_Clight: Language := mkLanguage Fundef_Clight V_type.

Lemma Fundef_Clight_type_of_fundef f: Fundef_sig Fundef_Clight f = Clight.type_of_fundef f.
Proof. unfold Fundef_sig. destruct f; auto. Qed.

Canonical Structure Language_Csharpminor: Language := mkLanguage (Fundef_common F_Csharpminor) V_unit.

Canonical Structure Language_Cminor: Language := mkLanguage (Fundef_common F_Cminor) V_unit.

Lemma Fundef_Cminor_funsig f: Fundef_sig (Fundef_common F_Cminor) f = Cminor.funsig f.
Proof. unfold Fundef_sig. destruct f; auto. Qed.

Canonical Structure Language_CminorSel: Language := mkLanguage (Fundef_common F_CminorSel) V_unit.

Lemma Fundef_CminorSel_funsig f: Fundef_sig (Fundef_common F_CminorSel) f = CminorSel.funsig f.
Proof. unfold Fundef_sig. destruct f; auto. Qed.

Canonical Structure Language_RTL: Language := mkLanguage (Fundef_common F_RTL) V_unit.

Lemma Fundef_RTL_funsig f: Fundef_sig (Fundef_common F_RTL) f = RTL.funsig f.
Proof. unfold Fundef_sig. destruct f; auto. Qed.

Canonical Structure Language_LTL: Language := mkLanguage (Fundef_common F_LTL) V_unit.
Canonical Structure Language_Linear: Language := mkLanguage (Fundef_common F_Linear) V_unit.
Canonical Structure Language_Mach: Language := mkLanguage (Fundef_common F_Mach) V_unit.
Canonical Structure Language_Asm: Language := mkLanguage (Fundef_common F_Asm) V_unit.
