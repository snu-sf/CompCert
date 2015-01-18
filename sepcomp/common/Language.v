Require Import RelationClasses.
Require String.
Require Import Coqlib Coqlib_linker.
Require Import Maps Maps_linker.
Require Import Integers Floats Values AST Globalenvs.
Require Import Errors Behaviors Compiler Smallstep Smallstep_linker.
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

Structure Fundef (sigT:Sig) (fT:F sigT) (efT:EF sigT) := mkFundef {
  Fundef_carrier :> Type;
  Fundef_dec: forall (fd:Fundef_carrier), fT + efT;
  HFundef_dec_inj: forall fd1 fd2 (Hfd: Fundef_dec fd1 = Fundef_dec fd2), fd1 = fd2;
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

Structure Language_ext: Type := mkLanguage_ext {
  lang :> Language;

  stateT: Type;
  contT: Type;
  mkCallstate: forall (cont:contT) (fd:lang.(fundefT)) (args:list val) (m:mem), stateT;
  mkReturnstate: forall (cont:contT) (v:val) (m:mem), stateT;
  empty_cont: contT;

  step: forall (ge:Genv.t lang.(fundefT) lang.(vT)) (state1:stateT) (evt:Events.trace) (state2:stateT), Prop;
  signature_main: lang.(sigT);
  initial_state := fun (p:lang.(progT)) (state:stateT) =>
                     exists b f m0,
                       let ge := Genv.globalenv p in
                       Genv.init_mem p = Some m0 /\
                       Genv.find_symbol ge p.(prog_main) = Some b /\
                       Genv.find_funct_ptr ge b = Some f /\
                       lang.(fundefT).(Fundef_sig) f = signature_main /\
                       state = (mkCallstate empty_cont f nil m0);
  final_state := fun (state:stateT) (r:int) =>
                   exists m,
                     state = mkReturnstate empty_cont (Vint r) m;
  semantics := fun (p:lang.(progT)) =>
                 Semantics step (initial_state p) final_state (Genv.globalenv p);

  Hfinal_not_progress: forall v m,
                         ~ exists ge evt state', step ge (mkReturnstate empty_cont v m) evt state';
  Hfinal_not_call: forall v m1,
                     ~ exists cont fd args m2, mkReturnstate empty_cont v m1 = mkCallstate cont fd args m2;
  HmkReturnstate_inj: forall cont1 v1 m1 cont2 v2 m2 (H: mkReturnstate cont1 v1 m1 = mkReturnstate cont2 v2 m2),
                        cont1 = cont2 /\ v1 = v2 /\ m1 = m2
}.

Lemma initial_state_unique lang p s1 s2
      (H1: lang.(initial_state) p s1)
      (H2: lang.(initial_state) p s2):
  s1 = s2.
Proof.
  destruct H1 as [b [f [m0 [Hm0 [Hb [Hf [Hsig ?]]]]]]]. subst.
  destruct H2 as [b' [f' [m0' [Hm0' [Hb' [Hf' [Hsig' ?]]]]]]]. subst.
  rewrite Hm0 in Hm0'. inv Hm0'. rewrite Hb in Hb'. inv Hb'. rewrite Hf in Hf'. inv Hf'.
  auto.
Qed.

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
  mkFundef F_C EF_external_function_ext
           (fun fd =>
              match fd with
                | Csyntax.Internal f => inl f
                | Csyntax.External ef targs tres cc => inr (ef, targs, tres, cc)
              end) _.
Next Obligation. destruct fd1, fd2; inv Hfd; auto. Qed.
Program Canonical Structure Fundef_Clight: Fundef F_Clight EF_external_function_ext :=
  mkFundef F_Clight EF_external_function_ext
           (fun fd =>
              match fd with
                | Clight.Internal f => inl f
                | Clight.External ef targs tres cc => inr (ef, targs, tres, cc)
              end) _.
Next Obligation. destruct fd1, fd2; inv Hfd; auto. Qed.
Program Canonical Structure Fundef_common (fT:F Sig_signature): Fundef fT EF_external_function :=
  mkFundef fT EF_external_function
           (fun fd =>
              match fd with
                | AST.Internal f => inl f
                | AST.External ef => inr ef
              end) _.
Next Obligation. destruct fd1, fd2; inv Hfd; auto. Qed.

Canonical Structure V_type: V := mkV Ctypes.type_eq.
Canonical Structure V_unit: V := mkV unit_eq.

Canonical Structure Language_C: Language := mkLanguage Fundef_C V_type.
Program Canonical Structure Language_ext_C: Language_ext :=
  @mkLanguage_ext Language_C _ _
                  (fun k fd args m => Csem.Callstate fd args k m)
                  (fun k v m => Csem.Returnstate v k m)
                  Csem.Kstop
                  Cstrategy.step
                  (Ctypes.Tfunction Ctypes.Tnil Ctypes.type_int32s cc_default) _ _ _.
Next Obligation. intros [ge [evt [state' Hstep]]]. inv Hstep. inv H. inv H. Qed.

Lemma Fundef_C_type_of_fundef f: Fundef_sig Fundef_C f = Csyntax.type_of_fundef f.
Proof. unfold Fundef_sig, Fundef_dec. simpl. destruct f; auto. Qed.

Lemma initial_state_C_equiv p s:
  Language_ext_C.(initial_state) p s <-> Csem.initial_state p s.
Proof.
  constructor; intro X.
  - destruct X as [a [f [m0 [Hm0 [Ha [Hf [Hsig ?]]]]]]]. simpl in *. subst.
    econstructor; eauto. rewrite <- Fundef_C_type_of_fundef. auto.
  - inv X. repeat eexists; eauto.
    rewrite Fundef_C_type_of_fundef. auto.
Qed.

Lemma final_state_C_equiv s r:
  Language_ext_C.(final_state) s r <-> Csem.final_state s r.
Proof.
  constructor; intro X; inv X; simpl in *; econstructor; simpl; eauto.
Qed.

Lemma c_sem_implies2 c:
  forward_simulation (Cstrategy.semantics c) (Language_ext_C.(semantics) c).
Proof.
  apply semantics_compat; auto.
  - intros. rewrite initial_state_C_equiv. constructor; auto.
  - intros. rewrite final_state_C_equiv. constructor; auto.
Qed.


Canonical Structure Language_Clight: Language := mkLanguage Fundef_Clight V_type.
Program Canonical Structure Language_ext_Clight1: Language_ext :=
  @mkLanguage_ext Language_Clight _ _
                  (fun k fd args m => Clight.Callstate fd args k m)
                  (fun k v m => Clight.Returnstate v k m)
                  Clight.Kstop
                  Clight.step1
                  (Ctypes.Tfunction Ctypes.Tnil Ctypes.type_int32s cc_default) _ _ _.
Next Obligation. intros [ge [evt [state' Hstep]]]. inv Hstep. Qed.

Lemma Fundef_Clight_type_of_fundef f: Fundef_sig Fundef_Clight f = Clight.type_of_fundef f.
Proof. unfold Fundef_sig, Fundef_dec. simpl. destruct f; auto. Qed.

Lemma initial_state_Clight1_equiv p s:
  Language_ext_Clight1.(initial_state) p s <-> Clight.initial_state p s.
Proof.
  constructor; intro X.
  - destruct X as [a [f [m0 [Hm0 [Ha [Hf [Hsig ?]]]]]]]. simpl in *. subst.
    econstructor; eauto. rewrite <- Fundef_Clight_type_of_fundef. auto.
  - inv X. repeat eexists; eauto.
    rewrite Fundef_Clight_type_of_fundef. auto.
Qed.

Lemma final_state_Clight1_equiv p r:
  Language_ext_Clight1.(final_state) p r <-> Clight.final_state p r.
Proof.
  constructor; intro X; inv X; simpl in *; econstructor; simpl; eauto.
Qed.

Lemma clight1_sem_implies1 c:
  forward_simulation (Language_ext_Clight1.(semantics) c) (Clight.semantics1 c).
Proof.
  apply semantics_compat; auto.
  - intros. rewrite initial_state_Clight1_equiv. constructor; auto.
  - intros. rewrite final_state_Clight1_equiv. constructor; auto.
Qed.


Program Canonical Structure Language_ext_Clight2: Language_ext :=
  @mkLanguage_ext Language_Clight _ _
                  (fun k fd args m => Clight.Callstate fd args k m)
                  (fun k v m => Clight.Returnstate v k m)
                  Clight.Kstop
                  Clight.step2
                  (Ctypes.Tfunction Ctypes.Tnil Ctypes.type_int32s cc_default) _ _ _.
Next Obligation. intros [ge [evt [state' Hstep]]]. inv Hstep. Qed.


Canonical Structure Language_Csharpminor: Language := mkLanguage (Fundef_common F_Csharpminor) V_unit.
Program Canonical Structure Language_ext_Csharpminor: Language_ext :=
  @mkLanguage_ext Language_Csharpminor _ _
                  (fun k fd args m => Csharpminor.Callstate fd args k m)
                  (fun k v m => Csharpminor.Returnstate v k m)
                  Csharpminor.Kstop
                  Csharpminor.step
                  AST.signature_main _ _ _.
Next Obligation. intros [ge [evt [state' Hstep]]]. inv Hstep. Qed.


Canonical Structure Language_Cminor: Language := mkLanguage (Fundef_common F_Cminor) V_unit.
Program Canonical Structure Language_ext_Cminor: Language_ext :=
  @mkLanguage_ext Language_Cminor _ _
                  (fun k fd args m => Cminor.Callstate fd args k m)
                  (fun k v m => Cminor.Returnstate v k m)
                  Cminor.Kstop
                  Cminor.step
                  AST.signature_main _ _ _.
Next Obligation. intros [ge [evt [state' Hstep]]]. inv Hstep. Qed.

Lemma Fundef_Cminor_funsig f: Fundef_sig (Fundef_common F_Cminor) f = Cminor.funsig f.
Proof. unfold Fundef_sig, Fundef_dec. simpl. destruct f; auto. Qed.

Lemma initial_state_Cminor_equiv p s:
  Language_ext_Cminor.(initial_state) p s <-> Cminor.initial_state p s.
Proof.
  constructor; intro X.
  - destruct X as [a [f [m0 [Hm0 [Ha [Hf [Hsig ?]]]]]]]. simpl in *. subst.
    econstructor; eauto. rewrite <- Fundef_Cminor_funsig. auto.
  - inv X. repeat eexists; eauto.
    rewrite Fundef_Cminor_funsig. auto.
Qed.

Lemma final_state_Cminor_equiv p r:
  Language_ext_Cminor.(final_state) p r <-> Cminor.final_state p r.
Proof.
  constructor; intro X; inv X; simpl in *; econstructor; simpl; eauto.
Qed.

Lemma cminor_sem_implies2 rtl:
  forward_simulation (Cminor.semantics rtl) (Language_ext_Cminor.(semantics) rtl).
Proof.
  apply semantics_compat; auto.
  - intros. rewrite initial_state_Cminor_equiv. constructor; auto.
  - intros. rewrite final_state_Cminor_equiv. constructor; auto.
Qed.


Canonical Structure Language_CminorSel: Language := mkLanguage (Fundef_common F_CminorSel) V_unit.
Program Canonical Structure Language_ext_CminorSel: Language_ext :=
  @mkLanguage_ext Language_CminorSel _ _
                  (fun k fd args m => CminorSel.Callstate fd args k m)
                  (fun k v m => CminorSel.Returnstate v k m)
                  CminorSel.Kstop
                  CminorSel.step
                  AST.signature_main _ _ _.
Next Obligation. intros [ge [evt [state' Hstep]]]. inv Hstep. Qed.

Lemma Fundef_CminorSel_funsig f: Fundef_sig (Fundef_common F_CminorSel) f = CminorSel.funsig f.
Proof. unfold Fundef_sig, Fundef_dec. simpl. destruct f; auto. Qed.

Lemma initial_state_CminorSel_equiv p s:
  Language_ext_CminorSel.(initial_state) p s <-> CminorSel.initial_state p s.
Proof.
  constructor; intro X.
  - destruct X as [a [f [m0 [Hm0 [Ha [Hf [Hsig ?]]]]]]]. simpl in *. subst.
    econstructor; eauto. rewrite <- Fundef_CminorSel_funsig. auto.
  - inv X. repeat eexists; eauto.
    rewrite Fundef_CminorSel_funsig. auto.
Qed.

Lemma final_state_CminorSel_equiv p r:
  Language_ext_CminorSel.(final_state) p r <-> CminorSel.final_state p r.
Proof.
  constructor; intro X; inv X; simpl in *; econstructor; simpl; eauto.
Qed.

Lemma cminorsel_sem_implies1 rtl:
  forward_simulation (Language_ext_CminorSel.(semantics) rtl) (CminorSel.semantics rtl).
Proof.
  apply semantics_compat; auto.
  - intros. rewrite initial_state_CminorSel_equiv. constructor; auto.
  - intros. rewrite final_state_CminorSel_equiv. constructor; auto.
Qed.


Canonical Structure Language_RTL: Language := mkLanguage (Fundef_common F_RTL) V_unit.
Program Canonical Structure Language_ext_RTL: Language_ext :=
  @mkLanguage_ext Language_RTL _ _
                  RTL.Callstate
                  RTL.Returnstate
                  nil
                  RTL.step
                  AST.signature_main _ _ _.
Next Obligation. intros [ge [evt [state' Hstep]]]. inv Hstep. Qed.

Lemma Fundef_RTL_funsig f: Fundef_sig (Fundef_common F_RTL) f = RTL.funsig f.
Proof. unfold Fundef_sig, Fundef_dec. simpl. destruct f; auto. Qed.

Lemma initial_state_RTL_equiv p s:
  Language_ext_RTL.(initial_state) p s <-> RTL.initial_state p s.
Proof.
  constructor; intro X.
  - destruct X as [a [f [m0 [Hm0 [Ha [Hf [Hsig ?]]]]]]]. subst.
    econstructor; eauto. rewrite <- Fundef_RTL_funsig. auto.
  - inv X. repeat eexists; eauto.
    rewrite Fundef_RTL_funsig. auto.
Qed.

Lemma final_state_RTL_equiv p r:
  Language_ext_RTL.(final_state) p r <-> RTL.final_state p r.
Proof.
  constructor; intro X; inv X; simpl in *; econstructor; eauto.
Qed.

Lemma rtl_sem_implies1 rtl:
  forward_simulation (Language_ext_RTL.(semantics) rtl) (RTL.semantics rtl).
Proof.
  apply semantics_compat; auto.
  - intros. rewrite initial_state_RTL_equiv. constructor; auto.
  - intros. rewrite final_state_RTL_equiv. constructor; auto.
Qed.

Lemma rtl_sem_implies2 rtl:
  forward_simulation (RTL.semantics rtl) (Language_ext_RTL.(semantics) rtl).
Proof.
  apply semantics_compat; auto.
  - intros. rewrite initial_state_RTL_equiv. constructor; auto.
  - intros. rewrite final_state_RTL_equiv. constructor; auto.
Qed.


Canonical Structure Language_LTL: Language := mkLanguage (Fundef_common F_LTL) V_unit.
Canonical Structure Language_Linear: Language := mkLanguage (Fundef_common F_Linear) V_unit.
Canonical Structure Language_Mach: Language := mkLanguage (Fundef_common F_Mach) V_unit.
Canonical Structure Language_Asm: Language := mkLanguage (Fundef_common F_Asm) V_unit.
