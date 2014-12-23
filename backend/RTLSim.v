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
Require Import IndexedStep.
Require Import Op.
Require Import Registers.
Require Import RTL.
Require Import LinkerSpecification.
Require Import ProgramSim MemoryRelation.
Require Import ValueAnalysis_linker.

Set Implicit Arguments.

Definition is_normal_state (st:state): bool :=
  match st with
    | State _ _ _ _ _ _ => true
    | _ => false
  end.

Definition is_call (f:function) (pc:node): bool :=
  match (fn_code f)!pc with
    | Some (Icall _ _ _ _ _) => true
    | Some (Itailcall _ _ _) => true
    | _ => false
  end.

Definition state_mem (st:state): mem :=
  match st with
    | State _ _ _ _ _ m => m
    | Callstate _ _ _ m => m
    | Returnstate _ _ m => m
  end.

Section LSIM.

Variable (mrelT:Type).
Variable (mrelT_ops:mrelT_opsT mrelT).
Variable (main:positive).

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
    (Hfundef: fundef_weak_sim
                (@common_fundef_dec function) fn_sig
                (@common_fundef_dec function) fn_sig
                ge_src ge_tgt fundef_src fundef_tgt)
    (Hargs: list_forall2 (mrelT_ops.(sem_value) mrel) args_src args_tgt)
    (Hmrel: mrelT_ops.(sem) mrel mem_src mem_tgt)
    (Hreturn:
       forall mrel2 st2_src st2_tgt mem2_src mem2_tgt vres_src vres_tgt
              (Hvres: mrelT_ops.(sem_value) mrel2 vres_src vres_tgt)
              (Hst2_src: st2_src = Returnstate stack_src vres_src mem2_src)
              (Hst2_tgt: st2_tgt = Returnstate stack_tgt vres_tgt mem2_tgt)
              (Hsound_src: sound_state_ext fprog_src st2_src)
              (Hsound_tgt: sound_state_ext fprog_tgt st2_tgt)
              (Hmrel2_le: mrelT_ops.(le_public) mrel mrel2)
              (Hst2_mem: mrelT_ops.(sem) mrel2 mem2_src mem2_tgt),
       exists i2,
         state_lsim mrel2 i2 st2_src st2_tgt)
.

Inductive _state_lsim
          (state_lsim: mrelT -> WF.t -> state -> state -> Prop)
          (mrel:mrelT) (i:WF.t) (st_src st_tgt:state): Prop :=
| _state_lsim_return
    (Hsound_src: sound_state_ext fprog_src st_src)
    (Hsound_tgt: sound_state_ext fprog_tgt st_tgt)
    st2_src (Hst_src: star step ge_src st_src E0 st2_src)
    val2_src mem2_src (Hst2_src: st2_src = Returnstate cs_entry_src val2_src mem2_src)
    val_tgt mem_tgt (Hst_tgt: st_tgt = Returnstate cs_entry_tgt val_tgt mem_tgt)
    (mrel2:mrelT) (Hmrel2: mrelT_ops.(sem) mrel2 mem2_src mem_tgt)
    (Hmrel2_le: mrelT_ops.(le) mrel mrel2)
    (Hmrel2_le_public: mrelT_ops.(le_public) mrel_entry mrel2)

| _state_lsim_step
    (Hsound_src: sound_state_ext fprog_src st_src)
    (Hsound_tgt: sound_state_ext fprog_tgt st_tgt)
    (Hpreserve:
       forall evt st2_src (Hst2_src: step ge_src st_src evt st2_src),
         (exists i2 st2_tgt (mrel2:mrelT),
            plus step ge_tgt st_tgt evt st2_tgt /\
            mrelT_ops.(le) mrel mrel2 /\
            mrelT_ops.(sem) mrel2 (state_mem st2_src) (state_mem st2_tgt) /\
            _state_lsim_or_csim state_lsim mrel2 i2 st2_src st2_tgt) \/
         (exists i2 (mrel2:mrelT),
            WF.rel i2 i /\
            evt = E0 /\
            mrelT_ops.(le) mrel mrel2 /\
            mrelT_ops.(sem) mrel2 (state_mem st2_src) (state_mem st_tgt) /\
            _state_lsim_or_csim state_lsim mrel2 i2 st2_src st_tgt))
.
Hint Constructors _state_lsim.

Lemma state_lsim_mon: monotone4 _state_lsim.
Proof.
  repeat intro; destruct IN; eauto.
  - eapply _state_lsim_step; eauto.
    intros. exploit Hpreserve; eauto.
    intros [|]; intros; [left|right].
    + destruct H as [i2 [st2_tgt [mrel2 [Hstep [Hle [Hmrel Hsim]]]]]].
      eexists. eexists. eexists.
      repeat split; eauto.
      inv Hsim.
      * apply _state_lsim_or_csim_lsim. eauto.
      * eapply _state_lsim_or_csim_csim; eauto.
        intros. exploit Hreturn; eauto.
        intros [i3 Hsim]. exists i3. auto.
    + destruct H as [i2 [mrel2 [Hi2 [Hevt [Hle [Hmrel Hsim]]]]]].
      eexists. eexists.
      repeat split; eauto.
      inv Hsim.
      * apply _state_lsim_or_csim_lsim. eauto.
      * eapply _state_lsim_or_csim_csim; eauto.
        intros. exploit Hreturn; eauto.
        intros [i3 Hsim]. exists i3. auto.
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
         (Hmrel_entry: mrelT_ops.(sem) mrel_entry mem_entry_src mem_entry_tgt)
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
