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
Require Import RTL.
Require Import LinkerSpecification.
Require Import ProgramLSim.
Require Import ValueAnalysis_linker.

Set Implicit Arguments.

Definition state_mem (st:state): mem :=
  match st with
    | State _ _ _ _ _ m => m
    | Callstate _ _ _ m => m
    | Returnstate _ _ m => m
  end.

(* memory relation *)

Record mrelT_opsT (t:Type): Type := mkmrelT_opsT {
  sem :> t -> forall (p1 p2:program) (i:WF.t) (s1 s2:state), Prop;
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
      v = Vint i

}.

(* memory relation - equals *)

Definition mrelT_ops_equals: mrelT_opsT unit :=
  mkmrelT_opsT
    (fun _ _ _ _ s1 s2 => state_mem s1 = state_mem s2)
    (fun _ v1 v2 => Val.lessdef v1 v2)
    (fun _ _ => True)
    (fun _ _ => True).

Program Definition mrelT_props_equals: mrelT_propsT mrelT_ops_equals := mkmrelT_propsT _ _ _ _ _.
Next Obligation. repeat constructor. Qed.
Next Obligation. repeat constructor. Qed.
Next Obligation. inv H. auto. Qed.

(* memory relation - extends *)

Definition mrelT_ops_extends: mrelT_opsT unit :=
  mkmrelT_opsT
    (fun _ _ _ _ s1 s2 => Mem.extends (state_mem s1) (state_mem s2))
    (fun _ v1 v2 => Val.lessdef v1 v2)
    (fun _ _ => True)
    (fun _ _ => True).

Program Definition mrelT_props_extends: mrelT_propsT mrelT_ops_extends := mkmrelT_propsT _ _ _ _ _.
Next Obligation. repeat constructor. Qed.
Next Obligation. repeat constructor. Qed.
Next Obligation. inv H. auto. Qed.

Lemma mrelT_ops_extends_lessdef_list mrel v1 v2:
  Val.lessdef_list v1 v2 <-> list_forall2 (mrelT_ops_extends.(sem_value) mrel) v1 v2.
Proof.
  revert v2.
  induction v1; intros; constructor; intro H; inv H; constructor; auto.
  - apply IHv1. auto.
  - apply IHv1. auto.
Qed.

Section LSIM.

Variable (mrelT:Type).
Variable (mrelT_ops:mrelT_opsT mrelT).

Variable (fprog_src fprog_tgt:program).

Let ge_src := Genv.globalenv fprog_src.
Let ge_tgt := Genv.globalenv fprog_tgt.

Section STATE_LSIM.

Variable (cs_entry_src cs_entry_tgt:list stackframe).
Variable (mrel_entry:mrelT).

Inductive _state_lsim_or_csim
          (state_lsim: mrelT -> WF.t -> state -> state -> Prop)
          (mrel:mrelT) (i:WF.t) (st_src st_tgt:state): Prop :=
| _state_lsim_or_csim_lsim
    (Hlsim: state_lsim mrel i st_src st_tgt)
| _state_lsim_or_csim_csim
    stack_src fundef_src args_src mem_src
    (Hst_src: st_src = Callstate stack_src fundef_src args_src mem_src)
    stack_tgt fundef_tgt args_tgt mem_tgt
    (Hst_tgt: st_tgt = Callstate stack_tgt fundef_tgt args_tgt mem_tgt)
    (Hfundef: fundef_weak_lsim
                (@common_fundef_dec function) fn_sig
                (@common_fundef_dec function) fn_sig
                ge_src ge_tgt fundef_src fundef_tgt)
    (Hargs: list_forall2 (mrelT_ops.(sem_value) mrel) args_src args_tgt)
    (Hmrel: mrelT_ops.(sem) mrel fprog_src fprog_tgt i st_src st_tgt)
    (Hreturn:
       forall mrel2 i2 st2_src st2_tgt mem2_src mem2_tgt vres_src vres_tgt
              (Hvres: mrelT_ops.(sem_value) mrel2 vres_src vres_tgt)
              (Hst2_src: st2_src = Returnstate stack_src vres_src mem2_src)
              (Hst2_tgt: st2_tgt = Returnstate stack_tgt vres_tgt mem2_tgt)
              (Hsound_src: sound_state_ext fprog_src st2_src)
              (Hsound_tgt: sound_state_ext fprog_tgt st2_tgt)
              (Hmrel2_le: mrelT_ops.(le_public) mrel mrel2)
              (Hst2_mem: mrelT_ops.(sem) mrel2 fprog_src fprog_tgt i2 st2_src st2_tgt),
         state_lsim mrel2 i2 st2_src st2_tgt)
.

Inductive _state_lsim
          (state_lsim: mrelT -> WF.t -> state -> state -> Prop)
          (mrel:mrelT) (i:WF.t) (st_src st_tgt:state): Prop :=
| _state_lsim_term
    rval
    (Hst_src: final_state st_src rval)
    (Hst_tgt: final_state st_tgt rval)

| _state_lsim_return
    (Hsound_src: sound_state_ext fprog_src st_src)
    (Hsound_tgt: sound_state_ext fprog_tgt st_tgt)
    val_src mem_src (Hst_src: st_src = Returnstate cs_entry_src val_src mem_src)
    val_tgt mem_tgt (Hst_tgt: st_tgt = Returnstate cs_entry_tgt val_tgt mem_tgt)
    (Hval: mrelT_ops.(sem_value) mrel val_src val_tgt)
    (Hmem: mrelT_ops.(sem) mrel fprog_src fprog_tgt i st_src st_tgt)
    (Hmrel_le_public: mrelT_ops.(le_public) mrel_entry mrel)

| _state_lsim_step
    (Hnfinal: forall r, ~ final_state st_src r)
    (Hsound_src: sound_state_ext fprog_src st_src)
    (Hsound_tgt: sound_state_ext fprog_tgt st_tgt)
    (Hpreserve:
       forall evt st2_src (Hst2_src: step ge_src st_src evt st2_src),
         exists i2 st2_tgt (mrel2:mrelT),
           (plus step ge_tgt st_tgt evt st2_tgt \/
            star step ge_tgt st_tgt evt st2_tgt /\ WF.rel i2 i) /\
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

Inductive function_lsim (func_src func_tgt:function): Prop :=
| function_lsim_intro
    (Hlsim:
       forall
         mrel_init
         mrel_entry mem_entry_src mem_entry_tgt
         cs_entry_src cs_entry_tgt
         args_src args_tgt
         st_src st_tgt
         i
         (Hmrel_init: True) (* TODO *)
         (Hmrel_entry_le: mrelT_ops.(le) mrel_init mrel_entry)
         (Hmrel_entry: mrelT_ops.(sem) mrel_entry fprog_src fprog_tgt i st_src st_tgt)
         (Hargs: list_forall2 (mrelT_ops.(sem_value) mrel_entry) args_src args_tgt)
         (Hst_src: st_src = (Callstate cs_entry_src (Internal func_src) args_src mem_entry_src))
         (Hst_tgt: st_tgt = (Callstate cs_entry_tgt (Internal func_tgt) args_tgt mem_entry_tgt))
         (Hsound_src: sound_state_ext fprog_src st_src)
         (Hsound_tgt: sound_state_ext fprog_tgt st_tgt),
         state_lsim
           cs_entry_src cs_entry_tgt mrel_entry
           mrel_entry i
           (Callstate cs_entry_src (Internal func_src) args_src mem_entry_src)
           (Callstate cs_entry_tgt (Internal func_tgt) args_tgt mem_entry_tgt))
.

End LSIM.
Hint Constructors _state_lsim.
Hint Resolve state_lsim_mon: paco.
