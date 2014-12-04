Require Import Coqlib.

Set Implicit Arguments.

Definition is_empty (X:Type) (l:list X): bool :=
  match l with
    | nil => true
    | _ => false
  end.
