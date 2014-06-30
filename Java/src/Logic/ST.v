Require Import ILogic ILInsts SepAlg BILogic BILInsts IBILogic SepAlgMap Maps String Rel ZArith.
Require Import RelationClasses Setoid Morphisms. 
Require Import MapInterface MapFacts.
Require Import Open Stack Subst Lang OpenILogic Pure ILEmbed PureInsts.
Require Import UUSepAlg SepAlgInsts.
Require Import Heap AssertionLogic Util Program Traces.

Inductive ST : Type :=
  | st_end : ST
  | st_send : var -> sasn -> ST -> ST
  | st_recv : var -> sasn -> ST -> ST 
  .
  
Definition STs := Map [stptr, ST].

Local Existing Instance MapSepAlgOps.
Local Existing Instance MapSepAlg.
Local Existing Instance MapEquiv.
Local Existing Instance EquivPreorder.
Local Existing Instance UUMapSepAlg.

Instance RelSTs : Rel STs := _.
Instance PreorderSTs : PreOrder (@rel STs RelSTs) := _.
Instance STsSepAlgOps : SepAlgOps STs := _.
Instance SepAlgSTs : SepAlg STs := _.
Instance UUSepAlgSTs : UUSepAlg STs := _.

Fixpoint dual_ST (st : ST) : ST :=
  match st with
  | st_end => st_end
  | st_send v P st' => st_recv v P (dual_ST st')
  | st_recv v P st' => st_send v P (dual_ST st')
  end.

Program Instance ST_Dual : Dual ST dual_ST := {
  dual_involutive := _
}.
Next Obligation.
  induction a; [ reflexivity | |];
  simpl; rewrite IHa; reflexivity.
Defined.

Fixpoint subst_ST (x : var) (v : val) (t : ST) : ST :=
  match t with
  | st_end => st_end
  | st_send x' A t' => st_send x' (apply_subst A (subst1 `v x)) (subst_ST x v t')
  | st_recv x' A t' => st_recv x' (apply_subst A (subst1 `v x)) (subst_ST x v t')
  end.

Fixpoint ST_append (l r : ST) : ST :=
  match l with
    | st_end => r
    | st_send v P l' => st_send v P (ST_append l' r)
    | st_recv v P l' => st_recv v P (ST_append l' r)
  end.

Definition STs_append (l r : STs) : STs :=
  mapi (fun k r' => match (find k l) with
    | Some l' => ST_append l' r'
    | None => r'
    end) r. 

Module STNotations.
  	(*Notation " x ':' t " := (has_ST x t) (at level 88, left associativity) : st_scope.*)
  	
	Notation " '!' x ',{' P '}.' t " := (st_send x P t) (at level 88, left associativity) : st_scope.
	Notation " '&' x ',{' P '}.' t " := (st_recv x P t) (at level 88, left associativity) : st_scope.

	Open Scope st_scope.

End STNotations.
