Require Import Coq.omega.Omega.
Require Import ChargeCore.Logics.Later.
Require Import ChargeCore.Logics.ILogic.
Require Import ChargeCore.Logics.ILEmbed.
Require Import ChargeCore.Logics.ILInsts.
Require Import Java.Language.Program.

(*
Local Existing Instance ILLaterNat.
Local Existing Instance ILLaterNatOps.
Local Existing Instance ILLaterPre.
Local Existing Instance ILLaterPreOps.
Local Existing Instance ILPre_Ops.
Local Existing Instance ILPre_ILogic.
*)

Definition spec := ILPreFrm Prog_sub (ILPreFrm ge Prop).

(*
Global Instance ILLOperatorsSpec : ILLOperators spec := _.
Global Instance ILogicOpsSpec : ILogicOps spec := _. 
Global Instance ILSpec : ILLater spec := _.
*)

Local Transparent ILPre_Ops.
Require Import Compare_dec.
Definition mk_spec (f: Program -> nat -> Prop)
  (Hnat: forall k P, f P (S k) -> f P k)
  (HSPred: forall k P P', Prog_sub P P' -> f P k -> f P' k) : spec.
  refine (mkILPreFrm (fun k => mkILPreFrm (f k) _) _).
Proof.
  + intros n m Hnk S'. generalize dependent m. induction n; intros.
    - assert (m = 0) by omega; subst. apply S'.
    - destruct (gt_eq_gt_dec m (S n)) as [[H | H] | H]; [| | omega].
      * apply IHn. apply Hnat. apply S'. omega.
      * subst. apply S'.
  + assert (forall k P P', Prog_sub P P' -> f P k -> f P' k) as HProg.
    intros k' P P' HPP' S'. eapply HSPred; eassumption. 
    intros p p' Hp'' n S'; simpl in *. eapply HProg; eassumption.
Defined.

Program Definition prog_spec (X : Program -> Prop) : spec :=
  mk_spec (fun (P : Program) _ => forall (Q : Program) , Prog_sub P Q -> X Q /\ valid_program Q = true) _ _.
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
  intros Q n HQ R HQR.
  specialize (HQ _ HQR).
  simpl in *. subst. intuition congruence.
Qed.
