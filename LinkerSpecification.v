Require Import RelationClasses.
Require String.
Require Import Coqlib Coqlib_linker.
Require Import Maps_linker.
Require Import Integers Floats Values AST Globalenvs.

Set Implicit Arguments.

(** Linker definition *)
Section LINKER.

Variable (F V:Type).  
Variable (V_dec: forall (v1 v2:V), {v1 = v2} + {v1 <> v2}).

(** `linkable a b` means we can remove `a` and take `b` when the two are linked. *)

Inductive globfun_linkable: forall (f1 f2:AST.fundef F), Prop :=
| globvar_linkable_ei (* TODO: type check? *)
    e1 i2:
    globfun_linkable (External e1) (Internal i2)
| globvar_linkable_ee e:
    globfun_linkable (External e) (External e)
.

Inductive globvar_linkable (v1 v2:globvar V): Prop :=
| globvar_linkable_intro
    (Hinfo: v1.(gvar_info) = v2.(gvar_info))
    (Hinit: v1.(gvar_init) = nil)
    (Hreadonly: v1.(gvar_readonly) = v2.(gvar_readonly))
    (Hvolatile: v1.(gvar_volatile) = v2.(gvar_volatile))
.

Inductive globdef_linkable: forall (g1 g2:globdef (AST.fundef F) V), Prop :=
| globdef_linkable_fun
    f1 f2 (Hv: globfun_linkable f1 f2):
    globdef_linkable (Gfun f1) (Gfun f2)
| globdef_linkable_var
    v1 v2 (Hv: globvar_linkable v1 v2):
    globdef_linkable (Gvar v1) (Gvar v2)
.


(** `linkable` decidabilities. *)

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


(** main definition *)

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

Definition link_prog (prog1 prog2:program (AST.fundef F) V): option (program (AST.fundef F) V) :=
  if ident_eq prog1.(prog_main) prog2.(prog_main)
  then
    match
      link_globdefs
        (PTree.unelements prog1.(prog_defs))
        (PTree.unelements prog2.(prog_defs))
    with
      | Some defs => Some (mkprogram (PTree.elements defs) prog1.(prog_main))
      | None => None
    end
  else None.
End LINKER.


(** linker specification (TODO) *)
