Require Import Later Program ILogic ILEmbed ILInsts.

Local Existing Instance ILLaterNat.
Local Existing Instance ILLaterNatOps.
Local Existing Instance ILLaterPre.
Local Existing Instance ILLaterPreOps.
Local Existing Instance ILPre_Ops.
Local Existing Instance ILPre_ILogic.

Definition spec1 := ILPreFrm ge Prop.
Definition spec := ILPreFrm Prog_wf_sub spec1.

Global Instance ILLOperatorsSpec1 : ILLOperators spec1 := _.
Global Instance ILogicOpsSpec1 : ILogicOps spec1 := _. 
Global Instance ILSpec1 : ILLater spec1 := _.

Global Instance ILLOperatorsSpec : ILLOperators spec := _.
Global Instance ILogicOpsSpec : ILogicOps spec := _. 
Global Instance ILSpec : ILLater spec := _.

Local Transparent ILPre_Ops.
Require Import Compare_dec.
Definition mk_spec (f: Prog_wf -> nat -> Prop)
  (Hnat: forall k P, f P (S k) -> f P k)
  (HSPred: forall k P P', Prog_wf_sub P P' -> f P k -> f P' k) : spec.
  refine (mkILPreFrm (fun k => mkILPreFrm (f k) _) _).
Proof.
  assert (forall k P P', Prog_wf_sub P P' -> f P k -> f P' k) as HProg.
  intros k P P' HPP' S'. eapply HSPred; eassumption. 
  intros p p' Hp'' n S'; simpl in *. eapply HProg; eassumption.
  Grab Existential Variables.
  intros n m Hnk S'. generalize dependent m. induction n; intros.
  + assert (m = 0) by omega; subst. apply S'.
  + destruct (gt_eq_gt_dec m (S n)) as [[H | H] | H]; [| | omega].
    * apply IHn. apply Hnat. apply S'. omega.
    * subst. apply S'.
Defined.

Program Definition prog_spec (X : Prog_wf -> Prop) : spec :=
  mk_spec (fun (P : Prog_wf) _ => forall (Q : Prog_wf) , Prog_wf_sub P Q -> X Q) _ _.
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

Lemma prog_eq_to_prop P (f : Prog_wf -> Prop) (H : f P) : prog_eq P |-- [prog] f.
Proof.
  intros Q n HQ R HQR.
  specialize (HQ _ HQR).
  simpl in *. subst. apply H.
Qed.
