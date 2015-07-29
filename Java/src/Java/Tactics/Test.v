Require Import Coq.Lists.List.
Check list_rec.
Definition list_case {A : Type} (lst : list A) (P : list A -> Type) 
  (f_nil : nil = lst -> P nil) (f_cons : forall x xs, x :: xs = lst -> P (x :: xs)) : P lst :=
  match lst as lst' return lst' = lst -> P lst' with
    | nil => f_nil
    | x :: xs => f_cons x xs
  end eq_refl.
Print list_rect.
Fixpoint test (xs : list Prop) :=
  list_rect _ True (fun x xs => x /\ test xs) xs.