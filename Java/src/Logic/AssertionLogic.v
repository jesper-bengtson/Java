Require Import ILogic ILInsts SepAlg SepAlgPfun BILogic BILInsts IBILogic SepAlgMap Maps String Rel.
Require Import RelationClasses Setoid Morphisms Program. 
Require Import MapInterface MapFacts.
Require Import Open Stack Lang Pure ILEmbed.

Local Existing Instance ILPre_Ops.
Local Existing Instance ILPre_ILogic.
(*
Local Existing Instance ILPartial_Ops.
Local Existing Instance ILPartial_Logic.
*)

Local Existing Instance ILFun_Ops.
Local Existing Instance ILFun_ILogic.
Local Existing Instance SAIBIOps.
Local Existing Instance SAIBILogic.
Local Existing Instance BILPre_Ops.
Local Existing Instance IBILPreLogic.
Local Existing Instance BILFun_Ops.
Local Existing Instance IBILFunLogic.

(*
Local Existing Instance BILPartial_Ops.
Local Existing Instance BILPartialLogic.
*)
Local Existing Instance MapSepAlgOps.
Local Existing Instance MapSepAlg.
Local Existing Instance MapEquiv.
Local Existing Instance EquivPreorder.

Definition heap := Map [ptr * field, val].

Definition heap_unit : heap := @map_unit _ _ _ val.

Instance RelHeap : Rel heap := _.
Instance PreorderHeap : PreOrder (@rel heap RelHeap) := _.
Instance HeapSepAlgOps : SepAlgOps heap := _.
Instance SepAlgHeap : SepAlg heap := _.

Definition asn1 := ILPreFrm (@rel heap subheap) Prop.
Definition asn2 := ILPreFrm ge asn1.
Definition asn := ILPreFrm Prog_wf_sub asn2.

Instance ILogicOpsAsn1 : ILogicOps asn1 := _.
Instance ILogicOpsAsn2 : ILogicOps asn2 := _.
Instance ILogicOpsAsn : ILogicOps asn := _.

Instance ILogicAsn1 : ILogic asn1 := _.
Instance ILogicAsn2 : ILogic asn2 := _.
Instance ILogicAsn : ILogic asn := _.

Instance BILOperatorsAsn1 : BILOperators asn1 := _.
Instance BILOperatorsAsn2 : BILOperators asn2 := _.
Instance BILOperatorsAsn : BILOperators asn := _.

Instance IBILogicAsn1 : IBILogic asn1 := _.
Instance IBILogicAsn2 : IBILogic asn2 := _.
Instance IBILogicAsn  : IBILogic asn := _.
Local Transparent ILPre_Ops.

Definition mk_asn (f: Prog_wf -> nat -> heap -> Prop)
  (Hnat: forall P k h, f P (S k) h -> f P k h)
  (HProg: forall P P' k h, Prog_wf_sub P P' -> f P k h -> f P' k h)
  (Hheap: forall P k h h', subheap h h' -> f P k h -> f P k h') : asn.
  refine (mkILPreFrm (fun P => mkILPreFrm (fun k => mkILPreFrm (fun h => f P k h) _) _) _).
Proof.
  intros P P' HP Hn h H; simpl.
  eapply HProg; eassumption.
Grab Existential Variables.
  assert (forall k' k P h, k' >= k -> f P k' h -> f P k h) as Hnat'.
  intros k k' P' h Hkk' S.  
  induction Hkk'. assumption.
  apply IHHkk'. apply Hnat. assumption.
  intros n n' Hn'' p S; simpl in *. eapply Hnat'; eassumption.
  intros h h' Hh H. eapply Hheap; eassumption.
Defined.

Program Definition pointsto_aux (x : ptr) (f : field) (v : val) : asn :=
  mk_asn (fun P k h => subheap ((empty val) [(x, f) <- v]) h) _ _ _.
Next Obligation.
  setoid_rewrite H in H0. assumption.
Qed.


Local Existing Instance EmbedILPreDropOpEq.
Local Existing Instance EmbedILPreDropEq.
Local Existing Instance EmbedILPreDropOpNeq.
Local Existing Instance EmbedILPreDropNeq.

Instance EmbedAsnPropOp : EmbedOp Prop asn := _.
Instance EmbedAsnProp : Embed Prop asn := _.

Program Definition pointsto (p : val) (f : field) (v : val) : asn :=
  (p <> null) /\\ pointsto_aux (val_to_ptr p) f v.

Definition sasn := @open var _ asn.

Instance ILOpsSAsn : ILogicOps sasn := _.
Instance ILogicSAsn : ILogic sasn := _.
Instance BILOperatorsSAsn : BILOperators sasn := _.
Instance BILogicSAsn : IBILogic sasn := _.

Local Existing Instance EmbedILFunDropOp.
Local Existing Instance EmbedILFunDrop.
Local Existing Instance EmbedILPreDropOpEq.
Local Existing Instance EmbedILPreDropEq.
Local Existing Instance EmbedILPreDropOpNeq.
Local Existing Instance EmbedILPreDropNeq.
Local Existing Instance EmbedILFunOp.
Local Existing Instance EmbedILFun.
Local Existing Instance EmbedILPreOp.
Local Existing Instance EmbedILPre.

Instance EmbedAsnPureOp : EmbedOp pure sasn := _.
Instance EmbedAsnPure : Embed pure sasn := _.

Require Import SpecLogic.

Instance EmbedAsnSpecOp : EmbedOp spec sasn := _.
Instance EmbedAsnSpec : Embed spec sasn := _.


