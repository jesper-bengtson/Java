Require Import Later Program ILogic ILEmbed ILInsts.

(*
Local Existing Instance ILLaterNat.
Local Existing Instance ILLaterNatOps.
Local Existing Instance ILLaterPre.
Local Existing Instance ILLaterPreOps.
Local Existing Instance ILPre_Ops.
Local Existing Instance ILPre_ILogic.
*)

Require Import AssertionLogic.

Definition spec := ILPreFrm Prog_sub (ILPreFrm ge (ILPreFrm extSP Prop)).

(*
Global Instance ILLOperatorsSpec : ILLOperators spec := _.
Global Instance ILogicOpsSpec : ILogicOps spec := _. 
Global Instance ILSpec : ILLater spec := _.
*)

Local Transparent ILPre_Ops.
Require Import Compare_dec.
Definition mk_spec (f: Program -> nat -> sasn -> Prop)
  (Hnat: forall k P T, f P (S k) T -> f P k T)
  (HSPred: forall k P P' T, Prog_sub P P' -> f P k T -> f P' k T)
  (HSExt: forall k P T U, extSP T U -> f P k T -> f P k U) : spec.
  refine (mkILPreFrm (fun k => (mkILPreFrm (fun P => (mkILPreFrm (fun T => f k P T)) _)) _) _).
Proof.
  intros P P' HPP' k. simpl. intros. eapply HSPred. eassumption. assumption.
  Grab Existential Variables.
  intros n m Hnk S'. simpl.
   generalize dependent m. induction n; intros.
  + assert (m = 0) by omega; subst. apply H.
  + destruct (gt_eq_gt_dec m (S n)) as [[H1 | H1] | H1]; [| | omega].
    * apply IHn. omega. apply Hnat. apply H.
    * subst. apply H.
  + intros; simpl. apply HSExt; assumption.

Defined.

Program Definition prog_spec (X : Program -> Prop) : spec :=
  mk_spec (fun (P : Program) _ _ => forall (Q : Program) , Prog_sub P Q -> X Q /\ valid_program Q = true) _ _ _.
Next Obligation.
  intros; apply H0; etransitivity; eassumption.
Qed.

Notation "'[prog]' P"    := (prog_spec  P) (at level 65).

Local Existing Instance EmbedILPreDropOp.
Local Existing Instance EmbedILPreDrop.
Local Existing Instance EmbedOpPropProp.
Local Existing Instance EmbedPropProp.

Instance EmbedPropSpecOp : EmbedOp Prop spec := _. 
Instance EmbedPropSpec : Embed Prop spec := _.

Definition prog_eq Prog : spec := [prog] (fun P => P = Prog).

Lemma prog_eq_to_prop P (f : Program -> Prop) (H : f P) : prog_eq P |-- [prog] f.
Proof.
  intros Q n T HQ R HQR.
  specialize (HQ _ HQR).
  simpl in *. subst. intuition congruence.
Qed.
