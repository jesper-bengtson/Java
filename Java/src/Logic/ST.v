Require Import ILogic ILInsts SepAlg BILogic BILInsts IBILogic SepAlgMap Maps String Rel.
Require Import RelationClasses Setoid Morphisms Program. 
Require Import MapInterface MapFacts.
Require Import Open Stack Subst Lang OpenILogic Pure ILEmbed PureInsts.
Require Import UUSepAlg SepAlgInsts.
Require Import Heap AssertionLogic Traces SemCmd SemCmdRules.

Inductive ST : Type :=
  | st_end : ST
  | st_send : var -> sasn -> ST -> ST
  | st_recv : var -> sasn -> ST -> ST 
  .

Definition STs := Map [stptr, ST].

Definition singleton_STs (x : var) (st: open ST) : open STs := fun s => add (val_to_stptr (s x)) (st s) (empty _).

Fixpoint subst_ST (x : var) (v : val) (t : ST) : ST :=
  match t with
  | st_end => st_end
  | st_send x' A t' => st_send x' (apply_subst A (subst1 `v x)) (subst_ST x v t')
  | st_recv x' A t' => st_recv x' (apply_subst A (subst1 `v x)) (subst_ST x v t')
  end.

Definition prune_STs (x : var) (st: open STs) : open STs := fun s => 
	match (s x) with
	  | vst c => remove c (st s)
	  | _ => st s
	end.

Definition subst_STs (x : var) (v : val) (t : STs) : STs := map (subst_ST x v) t.

Inductive ST_trace : Prog_wf -> traces -> ST -> trace -> Prop :=
  | stt_init : forall (p : Prog_wf) (trs : traces), ST_trace p trs st_end tinit
  | stt_send : forall (p : Prog_wf) (trs : traces) (t : ST) (v : val) (h : heap) (tr : trace)
  			   (HGuard: forall (x : var) (A : sasn) (t' : ST),
  			     t = (st_send x A t') ->
  			     (apply_subst A (subst1 `v  x)) (stack_empty var) trs p O h -> 
  			     ST_trace p trs (subst_ST x v t') tr
  			   ),
               ST_trace p trs t (tsend v h tr)
  | stt_recv : forall (p : Prog_wf) (trs : traces) (t : ST) (v : val) (h : heap) (tr : trace)
  			   (HGuard: forall (x : var) (A : sasn) (t' : ST),
  			     t = (st_recv x A t') ->
  			     (apply_subst A (subst1 `v  x)) (stack_empty var) trs p O h /\ 
  			     ST_trace p trs (subst_ST x v t') tr
  			   ),
               ST_trace p trs t (trecv v h tr)
  .

Local Transparent ILPre_Ops.
Local Transparent ILFun_Ops.
Local Transparent BILPre_Ops.
Local Transparent BILFun_Ops.

Instance ST_trace_m : Proper (eq ==> Equal ==> eq ==> eq ==> iff) ST_trace.
Proof.
  intros P P' HPP' trs trs' HtrsEqual tr tr' Htreq t t' Hteq.
  split; intro Hstt; subst.
  - induction Hstt.
    * apply stt_init.
    * apply stt_send.
      intros.
      apply H with (A := A); [ apply H0 | | apply HtrsEqual ].
      solve_model H1; [| congruence].
      symmetry; apply HtrsEqual.
    * apply stt_recv.
      intros.
      specialize (HGuard _ _ _ H).
      destruct HGuard as [HP Hstt].
      split.
      + solve_model HP; congruence.
      + admit (* fangel *).
  - induction Hstt.
    * apply stt_init.
    * apply stt_send.
      intros.
      apply H with (A := A); [ apply H0 | | apply HtrsEqual ].
      solve_model H1; congruence.
    * apply stt_recv.
      intros.
      specialize (HGuard _ _ _ H).
      destruct HGuard as [HP Hstt].
      split.
      + solve_model HP; congruence.
      + admit (* fangel *).
Qed.

Definition STs_traces (P : Prog_wf) (t : STs) (tr : traces) : Prop := forall k t', MapsTo k t' t -> exists tr', MapsTo k tr' tr /\ ST_trace P (remove k tr) t' tr'.


Program Definition has_ST (c : val) (t : ST) : tasn := 
  mk_tasn (fun trs => mk_asn (fun P k h => forall P' tr, Prog_wf_sub P P' -> MapsTo (val_to_stptr c) tr trs -> ST_trace P' (remove (val_to_stptr c) trs) t tr) _ _ _) _.
Next Obligation.
  assert (Prog_wf_sub P P'0).
    transitivity P'; assumption.
  apply H0; assumption.
Defined.
Next Obligation.
  rewrite <- H in H2.
  rewrite <- H.
  apply H0; assumption.
Defined.

Module STNotations.
 
	(* Notation " x ':' t " := (singleton_STs x t) (at level 88, left associativity) : st_scope. *)
 
	Notation " x ':' t " := (has_ST x t) (at level 88, left associativity) : st_scope.

	Notation " '!' x ',{' P '}.' t " := (st_send x P t) (at level 88, left associativity) : st_scope.
	Notation " '&' x ',{' P '}.' t " := (st_recv x P t) (at level 88, left associativity) : st_scope.

	Open Scope st_scope.

End STNotations.
