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
Require Import Op.
Require Import Registers.
Require Import Csyntax Csem Clight.
Require Import LinkerSpecification.
Require Import ProgramLSim.

Set Implicit Arguments.

Definition transf_V := fun (type:Ctypes.type) => Errors.OK type.

Definition signature_of_C_function (f:Csyntax.function) :=
  {| sig_args := map Ctypes.typ_of_type (map snd (Csyntax.fn_params f));
     sig_res  := Ctypes.opttyp_of_type (Csyntax.fn_return f);
     sig_cc   := Csyntax.fn_callconv f |}.

Lemma Clight_initial_state_unique p s1 s2
      (H1: Clight.initial_state p s1)
      (H2: Clight.initial_state p s2):
  s1 = s2.
Proof.
  inv H1. inv H2. unfold ge, ge0 in *.
  rewrite H in H1. inv H1. rewrite H0 in H5. inv H5. rewrite H3 in H6. inv H6.
  auto.
Qed.

Section FUTURE.

Variable (fprog:Csyntax.program).
Variable (ftprog:Clight.program).
Hypothesis (Hfsim: program_weak_lsim
                     C_fundef_dec signature_of_C_function
                     Clight_fundef_dec Cshmgen.signature_of_function
                     transf_V
                     fprog ftprog).

Let globfun_weak_lsim :=
  globfun_lsim
    C_fundef_dec signature_of_C_function
    Clight_fundef_dec Cshmgen.signature_of_function
    (fun _ _ _ _ => True)
    fprog ftprog.

Let ge := Genv.globalenv fprog.
Let tge := Genv.globalenv ftprog.

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof (symbols_preserved Hfsim).

Lemma varinfo_preserved:
  forall b, Genv.find_var_info tge b = Genv.find_var_info ge b.
Proof.
  intros. exploit varinfo_preserved.
  { instantiate (1 := ftprog). instantiate (1 := fprog). apply Hfsim. }
  instantiate (1 := b). unfold ge, tge.
  destruct (Genv.find_var_info (Genv.globalenv ftprog) b), (Genv.find_var_info (Genv.globalenv fprog) b); intros; auto; inv H.
  destruct g0; auto.
Qed.

Lemma funct_ptr_translated:
  forall (b: block) (f: Csyntax.fundef),
  Genv.find_funct_ptr ge b = Some f ->
  exists tf, Genv.find_funct_ptr tge b = Some tf /\
             fundef_weak_lsim
               C_fundef_dec signature_of_C_function
               Clight_fundef_dec Cshmgen.signature_of_function
               ge tge f tf.
Proof (funct_ptr_translated Hfsim).

Lemma functions_translated:
  forall (v: val) (f: Csyntax.fundef),
  Genv.find_funct ge v = Some f ->
  exists tf, Genv.find_funct tge v = Some tf /\
             fundef_weak_lsim
               C_fundef_dec signature_of_C_function
               Clight_fundef_dec Cshmgen.signature_of_function
               ge tge f tf.
Proof (functions_translated Hfsim).

Lemma block_is_volatile_preserved:
  forall b, block_is_volatile tge b = block_is_volatile ge b.
Proof.
  intros. unfold block_is_volatile. rewrite varinfo_preserved. auto.
Qed.

End FUTURE.

Record mrelT_opsT (t:Type): Type := mkmrelT_opsT {
  sem :> t -> forall (p1:Csyntax.program) (p2:Clight.program) (i:WF.t) (s1:Csem.state) (s2:Clight.state), Prop;
  sem_value :> t -> forall (v1 v2:val), Prop;
  le: t -> t -> Prop;
  le_public: t -> t -> Prop
}.

Record mrelT_propsT (t:Type) (ops:mrelT_opsT t): Prop := mkmrelT_propsT {
  le_preorder: PreOrder ops.(le);
  le_public_preorder: PreOrder ops.(le_public);
  le_public_le:
    forall mrel1 mrel2 (Hle_public: ops.(le_public) mrel1 mrel2),
      ops.(le) mrel1 mrel2;
  sem_value_int:
    forall mrel i v (H: ops.(sem_value) mrel (Vint i) v),
      v = Vint i;
  Hmrel_i_init:
    forall p1 p2 s1 s2
           (Hp: program_weak_lsim
                  C_fundef_dec signature_of_C_function
                  Clight_fundef_dec Cshmgen.signature_of_function
                  transf_V
                  p1 p2)
           (H1: Csem.initial_state p1 s1)
           (H2: Clight.initial_state p2 s2),
    exists mrel_init i_init,
      ops.(sem) mrel_init p1 p2 i_init s1 s2;
  Hexternal_call:
    forall p1 p2 s1 s2 ef targs1 targs2 tres1 tres2 cc1 cc2 args1 args2 cont1 cont2 m1 m2 evt s1' res1 m1' mrel i
           (Hp: program_weak_lsim
                  C_fundef_dec signature_of_C_function
                  Clight_fundef_dec Cshmgen.signature_of_function
                  transf_V
                  p1 p2)
           (Hs1: s1 = Csem.Callstate (Csyntax.External ef targs1 tres1 cc1) args1 cont1 m1)
           (Hs2: s2 = Clight.Callstate (Clight.External ef targs2 tres2 cc2) args2 cont2 m2)
           (Hs1': s1' = Csem.Returnstate res1 cont1 m1')
           (Hmrel: ops.(sem) mrel p1 p2 i s1 s2)
           (Hs2: Csem.step (Genv.globalenv p1) s1 evt s1')
           (Hargs: list_forall2 (ops.(sem_value) mrel) args1 args2),
    exists mrel' i' s2' res2 m2',
      s2' = Clight.Returnstate res2 cont2 m2' /\
      Clight.step1 (Genv.globalenv p2) s2 evt s2' /\
      ops.(sem) mrel' p1 p2 i' s1' s2' /\
      ops.(sem_value) mrel' res1 res2 /\
      ops.(le_public) mrel mrel'
}.

Section LSIM.

Variable (mrelT:Type).
Variable (mrelT_ops:mrelT_opsT mrelT).

Variable (fprog_src:Csyntax.program).
Variable (fprog_tgt:Clight.program).

Let ge_src := Genv.globalenv fprog_src.
Let ge_tgt := Genv.globalenv fprog_tgt.

Section STATE_LSIM.

Variable (cs_entry_src:Csem.cont).
Variable (cs_entry_tgt:Clight.cont).
Variable (mrel_entry:mrelT).

Inductive _state_lsim_or_csim
          (state_lsim: mrelT -> WF.t -> Csem.state -> Clight.state -> Prop)
          (mrel:mrelT) (i:WF.t) (st_src:Csem.state) (st_tgt:Clight.state): Prop :=
| _state_lsim_or_csim_lsim
    (Hlsim: state_lsim mrel i st_src st_tgt)
| _state_lsim_or_csim_csim
    stack_src fundef_src args_src mem_src
    (Hst_src: st_src = Csem.Callstate fundef_src args_src stack_src mem_src)
    stack_tgt fundef_tgt args_tgt mem_tgt
    (Hst_tgt: st_tgt = Clight.Callstate fundef_tgt args_tgt stack_tgt mem_tgt)
    (Hfundef: fundef_weak_lsim
                C_fundef_dec signature_of_C_function
                Clight_fundef_dec Cshmgen.signature_of_function
                ge_src ge_tgt fundef_src fundef_tgt)
    (Hargs: list_forall2 (mrelT_ops.(sem_value) mrel) args_src args_tgt)
    (Hmrel: mrelT_ops.(sem) mrel fprog_src fprog_tgt i st_src st_tgt)
    (Hreturn:
       forall mrel2 i2 st2_src st2_tgt mem2_src mem2_tgt vres_src vres_tgt
              (Hvres: mrelT_ops.(sem_value) mrel2 vres_src vres_tgt)
              (Hst2_src: st2_src = Csem.Returnstate vres_src stack_src mem2_src)
              (Hst2_tgt: st2_tgt = Clight.Returnstate vres_tgt stack_tgt mem2_tgt)
              (Hmrel2_le: mrelT_ops.(le_public) mrel mrel2)
              (Hst2_mem: mrelT_ops.(sem) mrel2 fprog_src fprog_tgt i2 st2_src st2_tgt),
         state_lsim mrel2 i2 st2_src st2_tgt)
.

Inductive _state_lsim
          (state_lsim: mrelT -> WF.t -> Csem.state -> Clight.state -> Prop)
          (mrel:mrelT) (i:WF.t) (st_src:Csem.state) (st_tgt:Clight.state): Prop :=
| _state_lsim_term
    rval
    (Hst_src: Csem.final_state st_src rval)
    (Hst_tgt: Clight.final_state st_tgt rval)

| _state_lsim_return
    val_src mem_src (Hst_src: st_src = Csem.Returnstate val_src cs_entry_src mem_src)
    val_tgt mem_tgt (Hst_tgt: st_tgt = Clight.Returnstate val_tgt cs_entry_tgt mem_tgt)
    (Hval: mrelT_ops.(sem_value) mrel val_src val_tgt)
    (Hmem: mrelT_ops.(sem) mrel fprog_src fprog_tgt i st_src st_tgt)
    (Hmrel_le_public: mrelT_ops.(le_public) mrel_entry mrel)

| _state_lsim_step
    (Hnfinal: forall r, ~ Csem.final_state st_src r)
    (Hpreserve:
       forall evt st2_src (Hst2_src: Csem.step ge_src st_src evt st2_src),
         exists i2 st2_tgt (mrel2:mrelT),
           (plus Clight.step1 ge_tgt st_tgt evt st2_tgt \/
            star Clight.step1 ge_tgt st_tgt evt st2_tgt /\ WF.rel i2 i) /\
           mrelT_ops.(le) mrel mrel2 /\
           mrelT_ops.(sem) mrel2 fprog_src fprog_tgt i2 st2_src st2_tgt /\
           _state_lsim_or_csim state_lsim mrel2 i2 st2_src st2_tgt)
.
Hint Constructors _state_lsim.

Lemma state_lsim_mon: monotone4 _state_lsim.
Proof.
  repeat intro; destruct IN; eauto.
  - eapply _state_lsim_step; eauto.
    intros. exploit Hpreserve; eauto. intros [i2 [st2_tgt [mrel2 [Hstep [Hle [Hmrel Hsim]]]]]].
    eexists. eexists. eexists. repeat (split; eauto).
    inv Hsim.
    + apply _state_lsim_or_csim_lsim. eauto.
    + eapply _state_lsim_or_csim_csim; eauto.
Qed.

Definition state_lsim: _ -> _ -> _ -> _ -> Prop :=
  paco4 _state_lsim bot4.

End STATE_LSIM.

Inductive function_lsim (func_src:Csyntax.function) (func_tgt:Clight.function): Prop :=
| function_lsim_intro
    (Hlsim:
       forall
         mrel_entry mem_entry_src mem_entry_tgt
         cs_entry_src cs_entry_tgt
         args_src args_tgt
         st_src st_tgt
         i
         (Hmrel_entry: mrelT_ops.(sem) mrel_entry fprog_src fprog_tgt i st_src st_tgt)
         (Hargs: list_forall2 (mrelT_ops.(sem_value) mrel_entry) args_src args_tgt)
         (Hst_src: st_src = (Csem.Callstate (Csyntax.Internal func_src) args_src cs_entry_src mem_entry_src))
         (Hst_tgt: st_tgt = (Clight.Callstate (Clight.Internal func_tgt) args_tgt cs_entry_tgt mem_entry_tgt)),
           state_lsim
           cs_entry_src cs_entry_tgt mrel_entry
           mrel_entry i
           (Csem.Callstate (Csyntax.Internal func_src) args_src cs_entry_src mem_entry_src)
           (Clight.Callstate (Clight.Internal func_tgt) args_tgt cs_entry_tgt mem_entry_tgt))
.

End LSIM.
Hint Constructors _state_lsim.
Hint Resolve state_lsim_mon: paco.
