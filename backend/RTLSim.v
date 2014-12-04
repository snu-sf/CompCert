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
Require Import MemoryRelation.

Definition state_mem (st:state): mem :=
  match st with
    | State _ _ _ _ _ m => m
    | Callstate _ _ _ m => m
    | Returnstate _ _ m => m
  end.

Section LSIM.

Variable (Mrel:Type).
Variable (Mrel_ops:MREL_ops Mrel).

Section LSIM_FUNC.

Variable (ge_src ge_tgt:genv).

Section LSIM_STATE.

Variable (cs_entry_src cs_entry_tgt:list stackframe).
Variable (mrel_entry:Mrel).

Inductive _lsim_state
          (lsim_state: Mrel -> WF.t -> state -> state -> Prop)
          (mrel:Mrel) (i:WF.t) (st_src st_tgt:state): Prop :=
| _lsim_state_error
    st2_src (Hst_src: star step ge_src st_src E0 st2_src)
    (Hnostep: nostep step ge_src st2_src)
| _lsim_state_return
    st2_src (Hst_src: star step ge_src st_src E0 st2_src)
    val2_src mem2_src (Hst2_src: st2_src = Returnstate cs_entry_src val2_src mem2_src)
    val_tgt mem_tgt (Hst_tgt: st_tgt = Returnstate cs_entry_tgt val_tgt mem_tgt)
    (mrel2:Mrel) (Hmrel2: Mrel_ops.(sem) mrel2 mem2_src mem_tgt)
    (Hmrel2_le: Mrel_ops.(le) mrel mrel2)
    (Hmrel2_le_public: Mrel_ops.(le_public) mrel_entry mrel2)
| _lsim_state_call
    st2_src (Hst_src: star step ge_src st_src E0 st2_src)
    res2_src fundef2_src sp2_src pc2_src rs2_src stack2_src fundef3_src args2_src mem2_src
    (Hst2_src: st2_src = Callstate ((Stackframe res2_src fundef2_src sp2_src pc2_src rs2_src)::stack2_src) fundef3_src args2_src mem2_src)
    res2_tgt fundef2_tgt sp2_tgt pc2_tgt rs2_tgt stack2_tgt fundef3_tgt args2_tgt mem2_tgt
    (Hst_tgt: st_tgt = Callstate ((Stackframe res2_tgt fundef2_tgt sp2_tgt pc2_tgt rs2_tgt)::stack2_tgt) fundef3_tgt args2_tgt mem2_tgt)
    (Hfundef2: True) (* TODO: fundef2_src and fundef_tgt shall be equivalent *)
    (Hargs: True) (* TODO: args2_src and args_tgt shall be equivalent *)
    (mrel2:Mrel) (Hmrel2: Mrel_ops.(sem) mrel2 mem2_src mem2_tgt)
    (Hmrel2_le: Mrel_ops.(le) mrel mrel2)
    (Hreturn:
       forall mrel3 st3_src st3_tgt mem3_src mem3_tgt vres_src vres_tgt
              (Hvres: True) (* TODO: vres shall be equivalent *)
              (Hst3_src: st3_src = State stack2_src fundef2_src sp2_src pc2_src (rs2_src#res2_src <- vres_src) mem3_src)
              (Hst3_tgt: st3_tgt = State stack2_tgt fundef2_tgt sp2_tgt pc2_tgt (rs2_tgt#res2_tgt <- vres_tgt) mem3_tgt)
              (Hmrel3_le: Mrel_ops.(le_public) mrel2 mrel3)
              (Hst3_mem: Mrel_ops.(sem) mrel3 mem3_src mem3_tgt),
       exists i3,
         lsim_state mrel3 i3 st3_src st3_tgt)

| _lsim_state_step
    (Hprogress: exists evt st2_tgt, step ge_tgt st_tgt evt st2_tgt)
    (Hpreserve:
       forall evt st3_tgt (Hst3_tgt: step ge_tgt st_tgt evt st3_tgt),
       exists st2_src,
         star step ge_src st_src E0 st2_src /\
       exists i3 st3_src,
         indexed_step step ge_src (Indexed.mk i st2_src) evt (Indexed.mk i3 st3_src) /\
       exists (mrel3:Mrel),
         Mrel_ops.(le) mrel mrel3 /\
         Mrel_ops.(sem) mrel3 (state_mem st3_src) (state_mem st3_tgt) /\
         lsim_state mrel3 i3 st3_src st3_tgt)
.
Hint Constructors _lsim_state.

Lemma lsim_state_mon: monotone4 _lsim_state.
Proof.
  repeat intro; destruct IN; eauto.
  - eapply _lsim_state_call; eauto.
    intros. exploit Hreturn; eauto.
    intros [i3 Hsim]. exists i3. auto.
  - eapply _lsim_state_step; eauto.
    intros. exploit Hpreserve; eauto.
    intros [st2_src [Hst2_src [i3 [st3_src [Hst3_src [mrel3 [Hmrel3_le [Hmrel3 Hr]]]]]]]].
    eexists. split; eauto.
    eexists. eexists. split; eauto.
Qed.

Definition lsim_state: _ -> _ -> _ -> _ -> Prop :=
  paco4 _lsim_state bot4.

End LSIM_STATE.

Definition lsim_func_aux
           mrel_init func_src func_tgt: Prop :=
  forall
    mrel_entry mem_entry_src mem_entry_tgt
    cs_entry_src cs_entry_tgt
    args_src args_tgt
    mem2_src mem2_tgt stk_src stk_tgt rs_src rs_tgt st_src st_tgt
    (Hmrel_entry_le: Mrel_ops.(le) mrel_init mrel_entry)
    (Hmrel_entry: Mrel_ops.(sem) mrel_entry mem_entry_src mem_entry_tgt)
    (Hargs: True) (* TODO: args_src and args_tgt shall be equivalent *)
    (Hstk_src: Mem.alloc mem_entry_src 0 func_src.(fn_stacksize) = (mem2_src, stk_src))
    (Hstk_tgt: Mem.alloc mem_entry_tgt 0 func_tgt.(fn_stacksize) = (mem2_tgt, stk_tgt))
    (Hrs_src: rs_src = init_regs args_src func_src.(fn_params))
    (Hrs_tgt: rs_tgt = init_regs args_tgt func_tgt.(fn_params))
    (Hst_src: st_src = State cs_entry_src func_src (Vptr stk_src Int.zero) func_src.(fn_entrypoint) rs_src mem2_src)
    (Hst_tgt: st_tgt = State cs_entry_tgt func_tgt (Vptr stk_tgt Int.zero) func_tgt.(fn_entrypoint) rs_tgt mem2_tgt),
  exists i,
    lsim_state
      cs_entry_src cs_entry_tgt mrel_entry
      mrel_entry i st_src st_tgt
.

Inductive lsim_func
          mrel_init func_src func_tgt: Prop :=
| lsim_func_intro
    (Hlsim_func_aux: lsim_func_aux mrel_init func_src func_tgt)
    (Hsig: func_src.(fn_sig) = func_tgt.(fn_sig))
.

End LSIM_FUNC.

Definition lsim prog_src prog_tgt: Prop :=
  let ge_src := Genv.globalenv prog_src in
  let ge_tgt := Genv.globalenv prog_tgt in
  forall st_tgt (Hinit_tgt: initial_state prog_tgt st_tgt),
  exists st_src,
    initial_state prog_src st_src /\
  exists mrel_init,
    Mrel_ops.(sem) mrel_init (state_mem st_src) (state_mem st_tgt) /\
    forall b func_tgt (Hfunc_tgt: Genv.find_funct_ptr ge_tgt b = Some (Internal func_tgt)),
    exists func_src,
      Genv.find_funct_ptr ge_src b = Some (Internal func_src) /\
      True /\ (* TODO: condition on mrel_init and ge_src/tgt. *)
      lsim_func ge_src ge_tgt mrel_init func_src func_tgt
.

End LSIM.

Hint Constructors _lsim_state.
Hint Resolve lsim_state_mon: paco.
