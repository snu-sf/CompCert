Require Import RelationClasses.
Require String.
Require Import Coqlib Coqlib_linker.
Require Import Maps_linker.
Require Import Integers Floats Values AST Globalenvs.

Set Implicit Arguments.

Section LINK.

Variable (F V:Type).  
Variable (V_dec: forall (v1 v2:V), {v1 = v2} + {v1 <> v2}).

Record module : Type := mkmodule {
  module_defs: PTree.t (globdef (AST.fundef F) V);
  module_main: option ident
}.


(* `linkable` and `lessdef` relations *)

Inductive option_lessdef {A:Type}: forall (a1 a2:option A), Prop :=
| option_lessdef_ns a: option_lessdef None (Some a)
| option_lessdef_ss a: option_lessdef (Some a) (Some a)
.

Inductive globfun_linkable: forall (f1 f2:AST.fundef F), Prop :=
| globvar_linkable_ei (* TODO: type check? *)
    e1 i2:
    globfun_linkable (External e1) (Internal i2)
| globvar_linkable_ee e:
    globfun_linkable (External e) (External e)
.

Definition globfun_lessdef (f1 f2:AST.fundef F): Prop :=
  f1 = f2 \/ globfun_linkable f1 f2.

Inductive globvar_linkable (v1 v2:globvar V): Prop :=
| globvar_lessdef_intro
    (Hinfo: v1.(gvar_info) = v2.(gvar_info))
    (Hinit: v1.(gvar_init) = nil)
    (Hreadonly: v1.(gvar_readonly) = v2.(gvar_readonly))
    (Hvolatile: v1.(gvar_volatile) = v2.(gvar_volatile))
.

Definition globvar_lessdef (v1 v2:globvar V): Prop :=
  v1 = v2 \/ globvar_linkable v1 v2.

Inductive globdef_linkable: forall (g1 g2:globdef (AST.fundef F) V), Prop :=
| globdef_linkable_fun
    f1 f2 (Hv: globfun_linkable f1 f2):
    globdef_linkable (Gfun f1) (Gfun f2)
| globdef_linkable_var
    v1 v2 (Hv: globvar_linkable v1 v2):
    globdef_linkable (Gvar v1) (Gvar v2)
.

Inductive globdef_lessdef: forall (g1 g2:globdef (AST.fundef F) V), Prop :=
| globdef_lessdef_fun
    f1 f2 (Hv: globfun_lessdef f1 f2):
    globdef_lessdef (Gfun f1) (Gfun f2)
| globdef_lessdef_var
    v1 v2 (Hv: globvar_lessdef v1 v2):
    globdef_lessdef (Gvar v1) (Gvar v2)
.

Inductive module_lessdef (m1 m2:module): Prop :=
| module_lessdef_intro
    (Hdefs: forall var def1 (Hsrc: PTree.get var m1.(module_defs) = Some def1),
            exists def2, PTree.get var m2.(module_defs) = Some def2 /\ globdef_lessdef def1 def2)
    (Hmain: option_lessdef m1.(module_main) m2.(module_main))
.


(* relation properties *)

Program Instance globfun_lessdef_PreOrder: PreOrder globfun_lessdef.
Next Obligation.
  intro f. left. auto.
Qed.
Next Obligation.
  intros f1 f2 f3 H12 H23.
  destruct H12, H23; subst; auto.
  { left. auto. }
  { right. auto. }
  { right. auto. }
  inv H; inv H0.
  - right. apply globvar_linkable_ei.
  - right. apply globvar_linkable_ee.
Qed.

Lemma globdef_linkable_lessdef
      g1 g2 (Hlinkable: globdef_linkable g1 g2):
  globdef_lessdef g1 g2.
Proof.
  inv Hlinkable; constructor; auto.
  - right. auto.
  - right. auto.
Qed.

Program Instance globvar_lessdef_PreOrder: PreOrder globvar_lessdef.
Next Obligation.
  intros [info init readonly volatile].
  constructor; auto.
Qed.
Next Obligation.
  intros v1 v2 v3 H12 H23.
  destruct H12, H23; subst; auto.
  { left. auto. }
  { right. auto. }
  { right. auto. }
  right. inv H. inv H0.
  constructor; simpl.
  - rewrite Hinfo. auto.
  - destruct Hinit; subst; auto.
  - rewrite Hreadonly. auto.
  - rewrite Hvolatile. auto.
Qed.

Program Instance globdef_lessdef_PreOrder: PreOrder globdef_lessdef.
Next Obligation.
  intros [f|v]; constructor; reflexivity.
Qed.
Next Obligation.
  intros [f1|v1] [f2|v2] [f3|v3] H12 H23; inv H12; inv H23.
  - constructor. rewrite Hv. auto.
  - constructor. rewrite Hv. auto.
Qed.


(* relation decidabilities *)

Definition globfun_linkable_dec (f1 f2:AST.fundef F): {globfun_linkable f1 f2} + {~ globfun_linkable f1 f2}.
Proof.
  destruct f1 as [i1|e1].
  { right. intro X. inv X. }
  destruct f2 as [i2|e2].
  { left. constructor. }
  { destruct (external_function_eq e1 e2); [subst|].
    { left. constructor. }
    { right. contradict n. inv n; auto. }
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

Definition globdef_linkable_dec (g1 g2:globdef (AST.fundef F) V): {globdef_linkable g1 g2} + {~ globdef_linkable g1 g2}.
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


(* module operations *)

Definition link_main (main1 main2: option ident): option (option ident) :=
  match main1, main2 with
    | Some _, Some _ => None
    | Some _, None => Some main1
    | None, Some _ => Some main2
    | None, None => Some None
  end.

Definition link_globdefs (defs1 defs2:PTree.t (globdef (AST.fundef F) V)): option (PTree.t (globdef (AST.fundef F) V)) :=
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

Definition link_module (m1 m2:module): option module :=
  match link_globdefs m1.(module_defs) m2.(module_defs), link_main m1.(module_main) m2.(module_main) with
    | Some defs, Some main => Some (mkmodule defs main)
    | _, _ => None
  end.

Definition close_module (m:module) : option (program (AST.fundef F) V) :=
  match m.(module_main) with
    | None => None
    | Some main => Some (mkprogram (PTree.elements m.(module_defs)) main)
  end.


(* module operation properties *)

Lemma gflink_globdefs defs1 defs2 (Hlink: link_globdefs defs1 defs2 = None):
  exists var def1 def2,
    PTree.get var defs1 = Some def1 /\
    PTree.get var defs2 = Some def2 /\
    ~ globdef_linkable def1 def2 /\
    ~ globdef_linkable def2 def1.
Proof.
  unfold link_globdefs in Hlink.
  match goal with
    | [H: context[PTree_Properties.for_all ?m ?f] |- _] =>
      destruct (PTree_Properties.for_all m f) eqn:Hlinkable; inv Hlink
  end.
  apply PTree_Properties.for_all_false in Hlinkable.
  destruct Hlinkable as [i [x [Hx1 Hx2]]].
  destruct x; inv Hx2. rewrite PTree.gcombine in Hx1; auto.
  destruct (defs1 ! i) eqn:Hi1, (defs2 ! i) eqn:Hi2; inv Hx1.
  destruct (globdef_linkable_dec g g0); inv H0.
  destruct (globdef_linkable_dec g0 g); inv H1.
  repeat eexists; eauto.
Qed.

Lemma gtlink_globdefs defs1 defs2 defs (Hlink: link_globdefs defs1 defs2 = Some defs):
  forall var,
    match PTree.get var defs1, PTree.get var defs2, PTree.get var defs with
      | Some g1, Some g2, Some g =>
        (globdef_linkable g1 g2 /\ g2 = g) \/
        (globdef_linkable g2 g1 /\ g1 = g)
      | Some g1, None, Some g => g1 = g
      | None, Some g2, Some g => g2 = g
      | None, None, None => True
      | _, _, _ => False
    end.
Proof.
  intro i. unfold link_globdefs in Hlink.
  match goal with
    | [H: context[PTree_Properties.for_all ?m ?f] |- _] =>
      destruct (PTree_Properties.for_all m f) eqn:Hlinkable; inv Hlink
  end.
  rewrite PTree.goption_map, PTree.gcombine; auto.
  destruct (defs1 ! i) eqn:Hi1, (defs2 ! i) eqn:Hi2; auto.
  destruct (globdef_linkable_dec g g0).
  { left. split; auto. }
  destruct (globdef_linkable_dec g0 g).
  { right. split; auto. }
  eapply PTree_Properties.for_all_correct in Hlinkable; eauto.
  { instantiate (1 := None) in Hlinkable. inv Hlinkable. }
  instantiate (1 := i). rewrite PTree.gcombine; auto.
  rewrite Hi1, Hi2.
  destruct (globdef_linkable_dec g g0); try (contradict n; auto; fail).
  destruct (globdef_linkable_dec g0 g); try (contradict n0; auto; fail).
  auto.
Qed.

End LINK.


Section SIMULATION.

Variable (F_src F_tgt V:Type).
Variable (V_dec: forall (v1 v2:V), {v1 = v2} + {v1 <> v2}).

Parameter F_sim: forall (f_src:F_src) (f_tgt:F_tgt), Prop.

Inductive globfun_sim: forall (g_src:AST.fundef F_src) (g_tgt:AST.fundef F_tgt), Prop :=
| globfun_sim_i
    f_src f_tgt
    (Hf: F_sim f_src f_tgt):
    globfun_sim (Internal f_src) (Internal f_tgt)
| globfun_sim_e e:
    globfun_sim (External e) (External e)
.

Inductive globdef_sim: forall (g_src:globdef (AST.fundef F_src) V) (g_tgt:globdef (AST.fundef F_tgt) V), Prop :=
| globdef_sim_fun
    f_src f_tgt (Hf: globfun_sim f_src f_tgt):
    globdef_sim (Gfun f_src) (Gfun f_tgt)
| globdef_sim_var v:
    globdef_sim (Gvar v) (Gvar v)
.

Definition globdefs_sim
           (defs_src:PTree.t (globdef (AST.fundef F_src) V))
           (defs_tgt:PTree.t (globdef (AST.fundef F_tgt) V)):
  Prop :=
  forall i,
    match PTree.get i defs_src, PTree.get i defs_tgt with
      | Some g1, Some g2 => globdef_sim g1 g2
      | None, None => True
      | _, _ => False
    end.

Definition module_sim
           (m_src:module F_src V) (m_tgt:module F_tgt V): Prop :=
  globdefs_sim m_src.(module_defs) m_tgt.(module_defs) /\
  m_src.(module_main) = m_tgt.(module_main).

Definition program_sim
           (p_src:program (AST.fundef F_src) V) (p_tgt:program (AST.fundef F_tgt) V): Prop :=
  list_forall2
    (fun g_src g_tgt =>
       fst g_src = fst g_tgt /\
       globdef_sim (snd g_src) (snd g_tgt))
    p_src.(prog_defs) p_tgt.(prog_defs) /\
  p_src.(prog_main) = p_tgt.(prog_main).

Lemma link_globdefs_sim
      (defs1_src defs2_src:PTree.t (globdef (AST.fundef F_src) V))
      (defs1_tgt defs2_tgt:PTree.t (globdef (AST.fundef F_tgt) V))
      defs_src (Hdefs_src: link_globdefs V_dec defs1_src defs2_src = Some defs_src)
      (H1: globdefs_sim defs1_src defs1_tgt)
      (H2: globdefs_sim defs2_src defs2_tgt):
  exists defs_tgt,
    link_globdefs V_dec defs1_tgt defs2_tgt = Some defs_tgt /\
    globdefs_sim defs_src defs_tgt.
Proof.
  destruct (link_globdefs V_dec defs1_tgt defs2_tgt) eqn:Hdefs_tgt.
  { eexists. split; [eauto|].
    intro i. rename t into defs_tgt.
    eapply gtlink_globdefs in Hdefs_src. instantiate (1 := i) in Hdefs_src.
    eapply gtlink_globdefs in Hdefs_tgt. instantiate (1 := i) in Hdefs_tgt.
    specialize (H1 i). specialize (H2 i).
    destruct (defs1_src ! i) eqn:Hi1_src, (defs2_src ! i) eqn:Hi2_src, (defs_src ! i) eqn:Hi_src; subst; try (inv Hdefs_src; fail);
    destruct (defs1_tgt ! i) eqn:Hi1_tgt, (defs2_tgt ! i) eqn:Hi2_tgt, (defs_tgt ! i) eqn:Hi_tgt; subst; try (inv Hdefs_tgt; fail);
    try (inv H1; fail); try (inv H2; fail); auto.
    destruct Hdefs_src as [[]|[]], Hdefs_tgt as [[]|[]]; subst; auto.
    { inv H; inv H1; inv H2; inv H3; inv Hv; inv Hv0; try inv Hf; try inv Hf0.
      { repeat constructor. }
      { destruct v1, v2; simpl in *.
        rewrite Hinfo, Hinit, Hinit0, Hreadonly, Hvolatile.
        constructor.
      }
    }
    { inv H; inv H1; inv H2; inv H3; inv Hv; inv Hv0; try inv Hf; try inv Hf0.
      { repeat constructor. }
      { destruct v1, v2; simpl in *.
        rewrite Hinfo, Hinit, Hinit0, Hreadonly, Hvolatile.
        constructor.
      }
    }
  }
  { apply gflink_globdefs in Hdefs_tgt.
    destruct Hdefs_tgt as [i [def1 [def2 [Hdef1 [Hdef2 [H12 H21]]]]]].
    specialize (H1 i). rewrite Hdef1 in H1.
    destruct (defs1_src ! i) eqn:Hi1_src; [|inv H1].
    specialize (H2 i). rewrite Hdef2 in H2.
    destruct (defs2_src ! i) eqn:Hi2_src; [|inv H2].
    eapply gtlink_globdefs in Hdefs_src.
    instantiate (1 := i) in Hdefs_src.
    rewrite Hi1_src, Hi2_src in Hdefs_src.
    destruct (defs_src ! i) eqn:Hi_src; [|inv Hdefs_src].
    destruct Hdefs_src as [[]|[]]; subst.
    { inv H1; inv H2; inv H; try inv Hf; try inv Hf0.
      { inv Hv. }
      { inv Hv. }
      { contradict H12. repeat constructor. }
      { inv Hv. contradict H12. repeat constructor. }
      { contradict H12. constructor. auto. }
    }
    { inv H1; inv H2; inv H; try inv Hf; try inv Hf0.
      { inv Hv. }
      { contradict H21. repeat constructor. }
      { inv Hv. }
      { inv Hv. contradict H12. repeat constructor. }
      { contradict H21. constructor. auto. }
    }
  }
Qed.

Lemma link_module_sim
      (m1_src m2_src:module F_src V)
      (m1_tgt m2_tgt:module F_tgt V)
      m_src (Hm_src: link_module V_dec m1_src m2_src = Some m_src)
      (H1: module_sim m1_src m1_tgt)
      (H2: module_sim m2_src m2_tgt):
  exists m_tgt,
    link_module V_dec m1_tgt m2_tgt = Some m_tgt /\
    module_sim m_src m_tgt.
Proof.
  destruct m1_src as [defs1_src main1_src].
  destruct m1_tgt as [defs1_tgt main1_tgt].
  destruct m2_src as [defs2_src main2_src].
  destruct m2_tgt as [defs2_tgt main2_tgt].
  destruct H1 as [H1d H1m], H2 as [H2d H2m].
  unfold link_module in *. simpl in *. subst.
  destruct (link_globdefs V_dec defs1_src defs2_src) as [defs_src|] eqn:Hdef_src; [|inv Hm_src].
  destruct (link_main main1_tgt main2_tgt) as [main|] eqn:Hmain_src; inv Hm_src.
  exploit link_globdefs_sim; eauto.
  intros [defs_tgt [Hdefs_tgt Hsim]].
  rewrite Hdefs_tgt. eexists. split; eauto.
  split; auto.
Qed.
      
Lemma close_module_sim
      (m_src:module F_src V)
      (m_tgt:module F_tgt V)
      (p_src:program (AST.fundef F_src) V)
      (Hp_src: close_module m_src = Some p_src)
      (Hm: module_sim m_src m_tgt):
  exists p_tgt,
    close_module m_tgt = Some p_tgt /\
    program_sim p_src p_tgt.
Proof.
  destruct m_src as [defs_src main_src].
  destruct m_tgt as [defs_tgt main_tgt].
  unfold close_module in *. simpl in *.
  destruct main_src as [main_src|]; inv Hp_src.
  destruct Hm as [Hdefs Hmain]. simpl in *. subst.
  eexists. repeat split; eauto. simpl.
  apply PTree.elements_canonical_order; intros.
  - exploit Hdefs. instantiate (1 := i). rewrite H. intro X.
    destruct (defs_tgt ! i) eqn:Hi_tgt; [|inv X].
    eexists. split; eauto.
  - exploit Hdefs. instantiate (1 := i). rewrite H. intro X.
    destruct (defs_src ! i) eqn:Hi_src; [|inv X].
    eexists. split; eauto.
Qed.


Section PROGRAM_SIMULATION.

Variable (p_src: program (AST.fundef F_src) V).
Variable (p_tgt: program (AST.fundef F_tgt) V).
Variable (Hp: program_sim p_src p_tgt).

Lemma program_sim_match_program:
  match_program globfun_sim eq nil p_src.(prog_main) p_src p_tgt.
Proof.
  destruct Hp as [Hdefs Hmain].
  unfold match_program. split; eauto.
  exists p_tgt.(prog_defs). split; [|rewrite app_nil_r; auto].
  eapply list_forall2_imply; eauto. intros.
  destruct H1 as [H1 H2].
  destruct v1 as [var1 g1], v2 as [var2 g2]. simpl in *. subst.
  inv H2.
  - constructor. auto.
  - destruct v. constructor. auto.
Qed.

Lemma globalenvs_match:
  Genv.match_genvs globfun_sim eq nil (Genv.globalenv p_src) (Genv.globalenv p_tgt).
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
  forall (b : block) (f : AST.fundef F_src),
  Genv.find_funct_ptr (Genv.globalenv p_src) b = Some f ->
  exists tf : AST.fundef F_tgt,
  Genv.find_funct_ptr (Genv.globalenv p_tgt) b = Some tf /\ globfun_sim f tf.
Proof.
  generalize program_sim_match_program. intros Hmatch b f Hf.
  eapply Genv.find_funct_ptr_match; eauto.
Qed.

End PROGRAM_SIMULATION.

End SIMULATION.
