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
Require Import MemoryRelation.
Require Import ValueAnalysis_linker.
Require Import MemoryRelation ProgramSim RTLSim.

Set Implicit Arguments.

Section GLOBAL_SIM.

Variable (mrelT:Type).
Variable (mrelT_ops:mrelT_opsT mrelT).
Hypothesis (mrelT_props:mrelT_propsT mrelT_ops).

Variable (prog_src prog_tgt:program).
Hypothesis
  (Hsim:
     program_sim
       (@common_fundef_dec function) fn_sig
       (@common_fundef_dec function) fn_sig
       (@Errors.OK _)
       (function_lsim mrelT_ops)
       prog_src prog_tgt).

Variable (mrel_init:mrelT). (* TODO *)

Inductive match_stackframes: forall (mrel:mrelT) (cs_src cs_tgt:list stackframe), Prop :=
| match_stackframes_nil:
    match_stackframes mrel_init nil nil
| match_stackframes_cons
    ps_src ps_tgt s_src s_tgt
    pmrel mrel
    (Hp: match_stackframes pmrel ps_src ps_tgt)
    (Hmrel_le: mrelT_ops.(le) pmrel mrel)
    (Hreturn:
       forall rmrel st_src st_tgt mem_src mem_tgt vres_src vres_tgt
              (Hvres: mrelT_ops.(sem_value) rmrel vres_src vres_tgt)
              (Hst2_src: st_src = Returnstate s_src vres_src mem_src)
              (Hst2_tgt: st_tgt = Returnstate s_tgt vres_tgt mem_tgt)
              (Hsound_src: sound_state_ext prog_src st_src)
              (Hsound_tgt: sound_state_ext prog_tgt st_tgt)
              (Hmrel2_le: mrelT_ops.(le_public) mrel rmrel)
              (Hst2_mem: mrelT_ops.(sem) rmrel mem_src mem_tgt),
       exists ri,
         state_lsim mrelT_ops prog_src prog_tgt ps_src ps_tgt mrel rmrel ri st_src st_tgt):
    match_stackframes mrel s_src s_tgt
.

Inductive match_states (i:WF.t) (st_src st_tgt:state): Prop :=
| match_states_intro
    ps_src ps_tgt
    pmrel mrel
    (Hp: match_stackframes pmrel ps_src ps_tgt)
    (Hmrel_le: mrelT_ops.(le) pmrel mrel)
    (Hsound_src: sound_state_ext prog_src st_src)
    (Hsound_tgt: sound_state_ext prog_tgt st_tgt)
    (Hsim: state_lsim mrelT_ops prog_src prog_tgt ps_src ps_tgt pmrel mrel i st_src st_tgt)
.

Lemma program_sim_forward_simulation:
  forward_simulation (semantics prog_src) (semantics prog_tgt).
Proof.
  eapply (Forward_simulation
            (semantics prog_src)
            (semantics prog_tgt)
            WF.wf
            match_states).
  { admit. (* initial *)
  }
  { admit. (* final *)
  }
  { admit. (* step *)
  }
  { eapply symbols_preserved; eauto. }
Qed.

End GLOBAL_SIM.
