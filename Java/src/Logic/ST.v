Require Import ILogic ILInsts SepAlg BILogic BILInsts IBILogic SepAlgMap Maps String Rel ZArith.
Require Import RelationClasses Setoid Morphisms. 
Require Import MapInterface MapFacts.
Require Import Open Stack Subst Lang OpenILogic Pure ILEmbed PureInsts.
Require Import UUSepAlg SepAlgInsts.
Require Import Heap AssertionLogic Util Program.

Inductive ST : Type :=
  | st_end : ST
  | st_send : var -> sasn -> ST -> ST
  | st_recv : var -> sasn -> ST -> ST 
  .
  
Definition STs := Map [stptr, ST].

Fixpoint dual_ST (st : ST) : ST :=
  match st with
  | st_end => st_end
  | st_send v P st' => st_recv v P (dual_ST st')
  | st_recv v P st' => st_send v P (dual_ST st')
  end.

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

Program Instance ST_Dual : Dual ST dual_ST := {
  dual_involutive := _
}.
Next Obligation.
  induction a; [ reflexivity | |];
  simpl; rewrite IHa; reflexivity.
Qed.

Fixpoint subst_ST (x : var) (v : val) (t : ST) : ST :=
  match t with
  | st_end => st_end
  | st_send x' A t' => st_send x' (apply_subst A (subst1 `v x)) (subst_ST x v t')
  | st_recv x' A t' => st_recv x' (apply_subst A (subst1 `v x)) (subst_ST x v t')
  end.

Module Marshall.


	Inductive marshall (Pr : Prog_wf) (v : sval) (big : heap) : heap -> Prop :=
	  | marshall_int  : forall (z : Z) (m : heap)
	                       (Vint : v = vint z)
	                   (Msubheap : subheap m big),
	                   marshall Pr v big m
	  | marshall_bool : forall (b : bool) (m : heap)
	                       (Vbool : v = vbool b)
	                    (Msubheap : subheap m big),
	                    marshall Pr v big m
	  | marshall_ptr  : forall (ref : ptr) (cls : class) (pos : nat) (m : heap) fields
	                        (Vptr : v = vptr ref)
	                      (Vclass : ref = (pos, cls))
	                     (Vfields : field_lookup Pr cls fields)
	                       (Mhere : forall (f : field) (v' : sval),
	                                SS.In f fields ->
	                                MapsTo (ref, f) v' (get_heap_ptr big) /\
	                                MapsTo (ref, f) v' (get_heap_ptr m))
	                      (Mchild : forall (f : field) (v' : sval),
	                                SS.In f fields ->
	                                MapsTo (ref, f) v' (get_heap_ptr big) ->
	                                marshall Pr v' big m
	                      ),
	                     marshall Pr v big m.
	   (*            
	  | marshall_arr  : forall (ref : arrptr) (i : nat) (v' : sval) (m : heap)
	                    (Varr : v = varr ref)
	                    (Mmaps : MapsTo (ref, i) v' (get_heap_arr big))
	                    (Mmarshalls : marshall v' big m),
	                    marshall v big (heap_add_arr m ref i v')
	.*)
	
	Lemma marshall_from_smaller {Pr : Prog_wf} {a b m : heap} {v : sval}
	    (Hsubheap : subheap a b) (Hmarshall : marshall Pr v a m) :
	    marshall Pr v b m.
	Proof.
	    induction Hmarshall.
	    * eapply marshall_int; [eassumption | transitivity big; assumption].
	    * eapply marshall_bool; [eassumption | transitivity big; assumption].
	    * eapply marshall_ptr; try eassumption; intros f v' Hin; specialize (Mhere f v' Hin).
	      + destruct Mhere as [Minput Mres].
	        split; [| assumption].
	        destruct Hsubheap as [? Hsubheap].
	        eapply sa_mul_mapstoL; [apply Hsubheap | apply Minput].
	      + intro Hinput.
	        destruct Mhere as [Minput Mres].
	        eapply H; eassumption.
    Qed.

End Marshall.

Module STNotations.
  	(*Notation " x ':' t " := (has_ST x t) (at level 88, left associativity) : st_scope.*)
  	
	Notation " '!' x ',{' P '}.' t " := (st_send x P t) (at level 88, left associativity) : st_scope.
	Notation " '&' x ',{' P '}.' t " := (st_recv x P t) (at level 88, left associativity) : st_scope.

	Open Scope st_scope.

End STNotations.
