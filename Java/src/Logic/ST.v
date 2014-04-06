Require Import ILogic ILInsts SepAlg BILogic BILInsts IBILogic SepAlgMap Maps String Rel.
Require Import RelationClasses Setoid Morphisms. 
Require Import MapInterface MapFacts.
Require Import Open Stack Subst Lang OpenILogic Pure ILEmbed PureInsts.
Require Import UUSepAlg SepAlgInsts.
Require Import Heap AssertionLogic Traces Util Program.

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

Definition subst_STs (x : var) (v : val) (t : STs) : STs := map (subst_ST x v) t.

Inductive ST_trace : Prog_wf -> ST -> trace -> Prop :=
  | stt_init : forall (p : Prog_wf), ST_trace p st_end tinit
  | stt_send : forall (p : Prog_wf) (t : ST) (v : val) (h : heap) (tr : trace)
  			   (HGuard: forall (x : var) (A : sasn) (t' : ST),
  			     t = (st_send x A t') ->
  			     (apply_subst A (subst1 `v  x)) (stack_empty var) (empty _) p O h -> 
  			     ST_trace p (subst_ST x v t') tr
  			   ),
               ST_trace p t (tsend v h tr)
  | stt_recv : forall (p : Prog_wf) (t : ST) (v : val) (h : heap) (tr : trace)
  			   (HGuard: forall (x : var) (A : sasn) (t' : ST),
  			     t = (st_recv x A t') ->
  			     (apply_subst A (subst1 `v  x)) (stack_empty var) (empty _) p O h /\ 
  			     ST_trace p (subst_ST x v t') tr
  			   ),
               ST_trace p t (trecv v h tr)
  .

Inductive ST_trace_strong : Prog_wf -> ST -> trace -> Prop :=
  | stt_init_strong : forall (p : Prog_wf), ST_trace_strong p st_end tinit
  | stt_send_strong : forall (p : Prog_wf) (t : ST) (v : val) (h : heap) (x : var) (A : sasn) (tr : trace)
                      (HAsn : (apply_subst A (subst1 `v  x)) (stack_empty var) (empty _) p O h),
                      ST_trace_strong p (subst_ST x v t) tr ->
                      ST_trace_strong p (st_send x A t) (tsend v h tr)
  | stt_recv_strong : forall (p : Prog_wf) (t : ST) (v : val) (h : heap) (x : var) (A : sasn) (tr : trace)
                      (HAsn : (apply_subst A (subst1 `v  x)) (stack_empty var) (empty _) p O h),
                      ST_trace_strong p (subst_ST x v t) tr ->
                      ST_trace_strong p (st_recv x A t) (trecv v h tr)
  .

Lemma subst_ST_dual_comm : forall (t : ST) (x : var) (v : val),
	dual (subst_ST x v t) = subst_ST x v (dual t).
Proof.
  intros; unfold dual in *.
  induction t; simpl; [reflexivity |..];
  rewrite IHt; reflexivity.
Qed.

Lemma ST_trace_strong_dual : forall (p : Prog_wf) (t : ST) (tr : trace),
							 ST_trace_strong p t tr ->
							 ST_trace_strong p (dual t) (dual tr).
Proof.
  intros.
  induction H; constructor; try assumption;
  unfold dual in *; simpl;
  rewrite <- subst_ST_dual_comm;
  apply IHST_trace_strong.
Qed.

Lemma ST_trace_strong_weakening : forall (p : Prog_wf) (t : ST) (tr : trace),
							      ST_trace_strong p t tr ->
							      ST_trace        p t tr.
Proof.
  intros.
  induction H; constructor; intros;
  inversion H0; subst; [| split]; assumption.
Qed.

Local Transparent ILPre_Ops.
Local Transparent ILFun_Ops.
Local Transparent BILPre_Ops.
Local Transparent BILFun_Ops.

Instance ST_trace_strong_subprog_m : Proper (Prog_wf_sub ==> eq ==> eq ==> impl) ST_trace_strong.
Proof.
  intros P P' HPP st st' Htreq tr tr' Hteq H; subst.
  generalize dependent st'.
  induction tr'; intros st' H; inversion H; subst.
  - constructor.
  - constructor.
    solve_model HAsn; congruence.
    apply IHtr'; assumption.
  - constructor.
    solve_model HAsn; congruence.
    apply IHtr'; assumption.
Qed.

Definition STs_traces (P : Prog_wf) (t : STs) (tr : traces) : Prop := forall k t', 
  MapsTo k t' t -> exists tr', MapsTo k tr' tr /\ ST_trace P t' tr'.

Program Definition has_ST (c : expr) (t : open ST) : sasn := 
  fun s => mk_tasn (fun trs => mk_asn (fun P k h => forall P' tr, 
    Prog_wf_sub P P' -> 
    MapsTo (val_to_stptr (c s)) tr trs -> 
    ST_trace P' (t s) tr
  ) _ _ _) _.
Next Obligation.
  assert (Prog_wf_sub P P'0).
    transitivity P'; assumption.
  apply H0; assumption.
Defined.
Next Obligation.
  rewrite <- H in H2.
  apply H0; assumption.
Defined.

Module STNotations.
  	Notation " x ':' t " := (has_ST x t) (at level 88, left associativity) : st_scope.
  	
	Notation " '!' x ',{' P '}.' t " := (st_send x P t) (at level 88, left associativity) : st_scope.
	Notation " '&' x ',{' P '}.' t " := (st_recv x P t) (at level 88, left associativity) : st_scope.

	Open Scope st_scope.

End STNotations.
