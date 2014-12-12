Require Import RelationClasses.
Require String.
Require Import Coqlib Coqlib_linker.
Require Import Maps_linker.
Require Import Integers Floats Values AST Globalenvs.
Require Import LinkerSpecification LinkerProp Linkeq.
Require Import Errors.
Require Import paco.

Set Implicit Arguments.


(* lifting function simulation to program simulation *)
Section PROGRAM_SIM.

Variable (Fundef_src F_src EF_src V_src:Type).
Variable (fundef_src_dec: FundefDec Fundef_src F_src EF_src).
Variable (EF_src_dec: forall (v1 v2:EF_src), {v1 = v2} + {v1 <> v2}).
Variable (V_src_dec: forall (v1 v2:V_src), {v1 = v2} + {v1 <> v2}).

Variable (Fundef_tgt F_tgt EF_tgt V_tgt:Type).
Variable (fundef_tgt_dec: FundefDec Fundef_tgt F_tgt EF_tgt).
Variable (EF_tgt_dec: forall (v1 v2:EF_tgt), {v1 = v2} + {v1 <> v2}).
Variable (V_tgt_dec: forall (v1 v2:V_tgt), {v1 = v2} + {v1 <> v2}).

Variable (transf_EF: forall (ef:EF_src), res EF_tgt).
Variable (transf_V: forall (v:V_src), res V_tgt).
Definition V_sim (v_src:V_src) (v_tgt:V_tgt) := transf_V v_src = OK v_tgt.

Definition F_simT :=
  forall
    (defs_src:list (positive * globdef Fundef_src V_src))
    (defs_tgt:list (positive * globdef Fundef_tgt V_tgt))
    (f_src:F_src) (f_tgt:F_tgt), Prop.

Section CORE.

Variable (F_sim:F_simT).

Inductive globvar_sim (v_src:globvar V_src) (v_tgt:globvar V_tgt): Prop :=
| globvar_sim_intro
    (Hv: transf_globvar transf_V v_src = OK v_tgt)
.

(** simulation *)
Inductive globfun_sim
          (defs_src:list (positive * globdef Fundef_src V_src))
          (defs_tgt:list (positive * globdef Fundef_tgt V_tgt))
          (g_src:Fundef_src) (g_tgt:Fundef_tgt): Prop :=
| globfun_sim_i
    f_src f_tgt
    (Hsrc: fundef_src_dec g_src = inl f_src)
    (Htgt: fundef_tgt_dec g_tgt = inl f_tgt)
    (Hsim: forall fdefs_src fdefs_tgt
                  (Hfdefs_src: globdef_list_linkeq fundef_src_dec defs_src fdefs_src)
                  (Hfdefs_tgt: globdef_list_linkeq fundef_tgt_dec defs_tgt fdefs_tgt),
             F_sim fdefs_src fdefs_tgt f_src f_tgt)
| globfun_sim_e
    ef_src ef_tgt (Hef: transf_EF ef_src = OK ef_tgt)
    (Hsrc: fundef_src_dec g_src = inr ef_src)
    (Htgt: fundef_tgt_dec g_tgt = inr ef_tgt)
.

Inductive globdef_sim
          (defs_src:list (positive * globdef Fundef_src V_src))
          (defs_tgt:list (positive * globdef Fundef_tgt V_tgt)):
  forall (g_src:globdef Fundef_src V_src) (g_tgt:globdef Fundef_tgt V_tgt), Prop :=
| globdef_sim_fun
    f_src f_tgt (Hf: globfun_sim defs_src defs_tgt f_src f_tgt):
    globdef_sim defs_src defs_tgt (Gfun f_src) (Gfun f_tgt)
| globdef_sim_var
    v_src v_tgt (Hv: globvar_sim v_src v_tgt):
    globdef_sim defs_src defs_tgt (Gvar v_src) (Gvar v_tgt)
.

Definition globdef_list_sim
           (defs_src:list (positive * globdef Fundef_src V_src))
           (defs_tgt:list (positive * globdef Fundef_tgt V_tgt)):
  Prop :=
  list_forall2
    (fun g_src g_tgt =>
       fst g_src = fst g_tgt /\
       globdef_sim defs_src defs_tgt
                   (snd g_src) (snd g_tgt))
    defs_src defs_tgt.

Definition program_sim_aux
           (p_src:program Fundef_src V_src)
           (p_tgt:program Fundef_tgt V_tgt): Prop :=
  globdef_list_sim p_src.(prog_defs) p_tgt.(prog_defs) /\
  p_src.(prog_main) = p_tgt.(prog_main).

End CORE.

(** properties on F_sim and simulation *)
Lemma globfun_sim_le
      (F_sim1 F_sim2:F_simT) (HF_sim: F_sim1 <4= F_sim2):
  (globfun_sim F_sim1) <4= (globfun_sim F_sim2).
Proof.
  intros. inv PR.
  - eapply globfun_sim_i; eauto.
  - eapply globfun_sim_e; eauto.
Qed.

Lemma globdef_sim_le
      (F_sim1 F_sim2:F_simT) (HF_sim: F_sim1 <4= F_sim2):
  (globdef_sim F_sim1) <4= (globdef_sim F_sim2).
Proof.
  intros. inv PR.
  - eapply globdef_sim_fun; eauto.
    eapply globfun_sim_le; eauto.
  - eapply globdef_sim_var; eauto.
Qed.

Lemma globdef_list_sim_le
      (F_sim1 F_sim2:F_simT) (HF_sim: F_sim1 <4= F_sim2):
  (globdef_list_sim F_sim1) <2= (globdef_list_sim F_sim2).
Proof.
  intros.
  eapply list_forall2_imply; eauto. simpl. intros.
  destruct H1, v1, v2. simpl in *. subst.
  split; auto. eapply globdef_sim_le; eauto.
Qed.

Lemma program_sim_aux_le
      (F_sim1 F_sim2:F_simT) (HF_sim: F_sim1 <4= F_sim2):
  (program_sim_aux F_sim1) <2= (program_sim_aux F_sim2).
Proof.
  intros. destruct PR as [Hdefs Hmain]. split; auto.
  eapply globdef_list_sim_le; [|eauto]. auto.
Qed.

(** an instantiation of weak simulation: matching any function definitions *)
Definition globdef_list_weak_sim := globdef_list_sim (fun _ _ _ _ => True).

(** properties of linking on simulation *)
Ltac simplify_decs :=
  repeat
    match goal with
      | [Hl: fundef_src_dec ?f = _,
         Hr: fundef_src_dec ?f = _ |- _] =>
        rewrite Hl in Hr; inv Hr
      | [Hl: fundef_tgt_dec ?f = _,
         Hr: fundef_tgt_dec ?f = _ |- _] =>
        rewrite Hl in Hr; inv Hr
      | [Hl: transf_EF ?ef = _,
         Hr: transf_EF ?ef = _ |- _] =>
        rewrite Hl in Hr; inv Hr
    end.

Lemma link_globdef_list_sim
      (F_sim:F_simT)
      (defs1_src defs2_src:list (positive * globdef Fundef_src V_src))
      (defs1_tgt defs2_tgt:list (positive * globdef Fundef_tgt V_tgt))
      defs_src (Hdefs_src: link_globdef_list fundef_src_dec EF_src_dec V_src_dec defs1_src defs2_src = Some defs_src)
      (H1: globdef_list_sim F_sim defs1_src defs1_tgt)
      (H2: globdef_list_sim F_sim defs2_src defs2_tgt):
  exists defs_tgt,
    link_globdef_list fundef_tgt_dec EF_tgt_dec V_tgt_dec defs1_tgt defs2_tgt = Some defs_tgt /\
    globdef_list_sim F_sim defs_src defs_tgt.
Proof.
  admit.
Qed.

Section DEF.

Variable (F_sim:F_simT).

Definition program_sim :=
  program_sim_aux
    (fun defs_src defs_tgt f_src f_tgt =>
       forall (Hdefs: globdef_list_weak_sim defs_src defs_tgt),
       F_sim defs_src defs_tgt f_src f_tgt).

Lemma link_program_sim
      (p1_src p2_src:program Fundef_src V_src)
      (p1_tgt p2_tgt:program Fundef_tgt V_tgt)
      p_src (Hm_src: link_program fundef_src_dec EF_src_dec V_src_dec p1_src p2_src = Some p_src)
      (H1: program_sim p1_src p1_tgt)
      (H2: program_sim p2_src p2_tgt):
  exists m_tgt,
    link_program fundef_tgt_dec EF_tgt_dec V_tgt_dec p1_tgt p2_tgt = Some m_tgt /\
    program_sim p_src m_tgt.
Proof.
  destruct p1_src as [defs1_src main1_src].
  destruct p1_tgt as [defs1_tgt main1_tgt].
  destruct p2_src as [defs2_src main2_src].
  destruct p2_tgt as [defs2_tgt main2_tgt].
  destruct H1 as [H1d H1m], H2 as [H2d H2m].
  unfold link_program in *. simpl in *. subst.
  destruct ((main1_tgt =? main2_tgt)%positive) eqn:Hmain; [|inv Hm_src].
  apply Pos.eqb_eq in Hmain. subst.
  destruct (link_globdef_list fundef_src_dec EF_src_dec V_src_dec defs1_src defs2_src) as [defs_src|] eqn:Hdef_src; inv Hm_src.
  exploit link_globdef_list_sim; eauto.
  intros [defs_tgt [Hdefs_tgt Hsim]].
  rewrite Hdefs_tgt. eexists. split; eauto.
  split; auto.
Qed.

End DEF.

Section INITIALIZE.

Variable (F_sim:F_simT).
Variable (p_src: program Fundef_src V_src).
Variable (p_tgt: program Fundef_tgt V_tgt).
Variable (Hp: program_sim_aux F_sim p_src p_tgt).

Definition match_fundef :=
  globfun_sim
    F_sim
    p_src.(prog_defs)
    p_tgt.(prog_defs).

Lemma program_sim_match_program:
  match_program match_fundef V_sim nil p_src.(prog_main) p_src p_tgt.
Proof.
  destruct Hp as [Hdefs Hmain].
  unfold match_program. split; eauto.
  exists p_tgt.(prog_defs). split; [|rewrite app_nil_r; auto].
  eapply list_forall2_imply; eauto. intros.
  destruct H1 as [H1 H2].
  destruct v1 as [var1 g1], v2 as [var2 g2]. simpl in *. subst.
  inv H2.
  - constructor. auto.
  - inv Hv. destruct v_src. unfold transf_globvar in Hv0. simpl in Hv0.
    destruct (transf_V gvar_info) eqn:Hinfo; inv Hv0. simpl in *.
    constructor. auto.
Qed.

Lemma globalenvs_match:
  Genv.match_genvs match_fundef V_sim nil (Genv.globalenv p_src) (Genv.globalenv p_tgt).
Proof.
  generalize program_sim_match_program. intro Hmatch.
  eapply Genv.globalenvs_match; eauto; auto.
Qed.

Lemma program_sim_init_mem_match:
  forall m,
    Genv.init_mem p_src = Some m ->
    Genv.init_mem p_tgt = Some m.
Proof.
  generalize program_sim_match_program. intro Hmatch.
  intros. erewrite Genv.init_mem_match; eauto; auto.
Qed.

Theorem find_symbol_match:
  forall (s : ident),
  Genv.find_symbol (Genv.globalenv p_tgt) s = Genv.find_symbol (Genv.globalenv p_src) s.
Proof.
  generalize program_sim_match_program. intros Hmatch s.
  eapply Genv.find_symbol_match; eauto.
Qed.

Theorem find_funct_ptr_match:
  forall (b : block) (f : Fundef_src),
  Genv.find_funct_ptr (Genv.globalenv p_src) b = Some f ->
  exists tf : Fundef_tgt,
  Genv.find_funct_ptr (Genv.globalenv p_tgt) b = Some tf /\ match_fundef f tf.
Proof.
  generalize program_sim_match_program. intros Hmatch b f Hf.
  eapply Genv.find_funct_ptr_match; eauto.
Qed.

End INITIALIZE.

End PROGRAM_SIM.
