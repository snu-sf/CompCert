Require Import RelationClasses.
Require String.
Require Import Coqlib Coqlib_sepcomp.
Require Import Maps Maps_sepcomp.
Require Import Integers Floats Values AST Globalenvs.
Require Import Errors Behaviors Compiler Smallstep.
Require Import Language.

Set Implicit Arguments.

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
| globfun_linkable_ei
    e1 i2 (H1: fundef_dec f1 = inr e1) (H2: fundef_dec f2 = inl i2)
    (Hlinkable: is_true (efT.(EF_linkable) e1)) (Hsig: ef_sig e1 = f_sig i2)
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

Lemma globfun_linkable_dec (f1 f2:fundefT): {globfun_linkable f1 f2} + {~ globfun_linkable f1 f2}.
Proof.
  destruct (fundef_dec f1) as [i1|e1] eqn:Hf1.
  { right. intro X. inv X.
    - rewrite Hf1 in H1. inv H1.
    - rewrite Hf1 in H1. inv H1.
  }
  destruct (fundef_dec f2) as [i2|e2] eqn:Hf2.
  - destruct (sigT.(Sig_dec) (ef_sig e1) (f_sig i2)).
    + destruct (efT.(EF_linkable) e1) eqn:Hl.
      * left. econstructor; eauto.
      * right. intro X. inv X; clarify.
        rewrite Hl in Hlinkable. inv Hlinkable.
    + right. contradict n. inv n; clarify.
  - destruct (ef_dec e1 e2); [subst|].
    + left. eapply globfun_linkable_ee; eauto.
    + right. contradict n. inv n; clarify.
Defined.

Lemma init_data_dec (v1 v2:init_data): {v1 = v2} + {v1 <> v2}.
Proof.
  decide equality;
  (try apply Int.eq_dec);
  (try apply Int64.eq_dec);
  (try apply Float.eq_dec);
  (try apply Float32.eq_dec);
  (try apply zeq);
  (try apply ident_eq).
Defined.

Lemma globvar_linkable_dec (v1 v2:globvar vT): {globvar_linkable v1 v2} + {~ globvar_linkable v1 v2}.
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

Lemma globdef_linkable_dec (g1 g2:globdef fundefT vT): {globdef_linkable g1 g2} + {~ globdef_linkable g1 g2}.
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
