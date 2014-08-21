Require Import RelationClasses Setoid Morphisms Coq.Classes.Equivalence.
Require Import Lang Heap Rel Stack.
Open Scope equiv_scope.

Class Dual (A : Type) (dual : A -> A) : Prop := {
  dual_involutive : forall a : A, dual (dual a) === a
}.
Definition dual {A : Type} {dual' : A -> A} {D : Dual A dual'} (a : A) : A := dual' a.
Hint Unfold dual.

Lemma dual_isomorphic_aux {A : Type} {dual' : A -> A} {D : Dual A dual'} : forall (a b : A), a === b -> dual a === dual b.
Proof.
  intros.
  rewrite H; reflexivity.
Qed.

Lemma dual_isomorphic {A : Type} {dual' : A -> A} {D : Dual A dual'} : forall (a b : A), a === b <-> dual a === dual b.
Proof.
  split; intro H.
  * apply dual_isomorphic_aux; assumption.
  * apply dual_isomorphic_aux in H.
    repeat rewrite dual_involutive in H.
    assumption.
Qed.

Inductive trace : Type :=
  | t_end   : Lang.stack -> heap -> NS.t -> trace
  | t_fail  : trace
  | t_send  : stptr -> val -> heap -> trace -> trace
  | t_recv  : stptr -> (ptr -> heap -> trace) -> trace
  | t_start : stptr -> trace -> trace -> trace
  | t_tau : Lang.stack -> heap -> NS.t -> trace -> trace
  .
  
Fixpoint trace_safe (tr : trace) : Prop :=
	match tr with
		| t_end _ _ _ => True
		| t_fail => False
		| t_send _ _ _ tr' => trace_safe tr'
		| t_recv _ ftr => forall v h, trace_safe (ftr v h)
		| t_start _ _ tr' => trace_safe tr'
		| t_tau _ _ _ tr' => trace_safe tr'
	end.

Fixpoint fail_trace (tr : trace) : Prop :=
	match tr with
		| t_end _ _ _ => False
		| t_fail => True
		| t_send _ _ _ tr' => fail_trace tr'
		| t_recv _ ftr => exists v h, fail_trace (ftr v h)
		| t_start _ _ tr' => fail_trace tr'
		| t_tau _ _ _ tr' => fail_trace tr'
	end.
	
(*

Fixpoint dual_trace (t : trace) : trace := 
  match t with
    | t_end => t_end
    | t_start c t t' => t_start c t (dual_trace t')
    | t_send c v h t' => t_recv c v h (dual_trace t')
    | t_recv c v h t' => t_send c v h (dual_trace t')
    | t_tau tr => t_tau (dual_trace tr)
  end.

Program Instance trace_Dual : Dual trace dual_trace := {
  dual_involutive := _
}.
Next Obligation.
  induction a; [ reflexivity | ..]; simpl; try rewrite IHa; try rewrite IHa2; reflexivity.
Defined.

Fixpoint trace_append (l r : trace) : trace :=
  match l with
    | t_end => r
    | t_send c v h l' => t_send c v h (trace_append l' r)
    | t_recv c v h l' => t_recv c v h (trace_append l' r)
    | t_start c t l'  => t_start c t  (trace_append l' r)
    | t_tau l' => t_tau (trace_append l' r)
  end.
  
Fixpoint trace_length (l : trace) : nat :=
  match l with
    | t_end => O
    | t_send _ _ _ l' => S (trace_length l')
    | t_recv _ _ _ l' => S (trace_length l')
    | t_start _ l' l'' => S (trace_length l') + (trace_length l'')
    | t_tau l' => S (trace_length l')
  end.

Lemma trace_appendC : forall (a b c : trace), trace_append (trace_append a b) c = trace_append a (trace_append b c).
Proof.
  intros; induction a; simpl; try rewrite IHa; try rewrite IHa2; reflexivity.
Qed.  

Lemma trace_appendEndR : forall (a : trace), a = trace_append a t_end.
Proof.
  intros.
  induction a; [reflexivity | ..]; simpl; try rewrite <- IHa; try rewrite <- IHa2; reflexivity.
Qed.

Lemma trace_appendLength : forall tr tr', trace_length (trace_append tr tr') >= trace_length tr.
Proof.
  intros; induction tr; intros; simpl; omega.
Qed.
*)  