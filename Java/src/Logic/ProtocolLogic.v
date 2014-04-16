Require Import Rel Open ILogic ILInsts BILogic BILInsts IBILogic SepAlg SepAlgMap
               UUSepAlg SepAlgInsts OpenILogic Pure ILEmbed PureInsts Subst Stack.
Require Import Maps MapInterface MapFacts.
Require Import Lang ST AssertionLogic SpecLogic Util Program.

Definition PM := Map [protocol, ST].

Definition psasn := PM -> STs -> sasn.

Local Transparent ILPre_Ops.
Local Transparent ILFun_Ops.
Local Transparent BILPre_Ops.
Local Transparent BILFun_Ops.

Program Definition psasn_subst (P : psasn) (sub : subst) : psasn := 
  fun PM STs s => mk_asn (fun Pr k h => P PM STs (stack_subst s sub) Pr k h) _ _ _.
Next Obligation.
  solve_model H.
  congruence.
Defined.
Next Obligation.
  solve_model H0.
  congruence.
Defined.
Next Obligation.
  solve_model H0.
  congruence.
Defined.

Program Definition ST_exists (p : protocol) (T : ST) : psasn :=
  fun PM STs s => mk_asn (fun P k h =>
    MapsTo p T PM
  ) _ _ _.

Program Definition has_ST (v : var) (T : ST) : psasn :=
  fun PM STs s => mk_asn (fun P k h =>
    MapsTo (val_to_stptr (s v)) T STs
  ) _ _ _.

Program Definition has_subst_ST (x z y : var) (T : ST) : psasn :=
  fun PM STs s => mk_asn (fun P k h =>
    MapsTo (val_to_stptr (s x)) (subst_ST z (s y) T) STs
  ) _ _ _.

Program Definition all_STs (T : ST) : psasn :=
  fun PM STs s => mk_asn (fun P k h =>
    forall c, In c STs -> MapsTo c T STs
  ) _ _ _.

Local Existing Instance ILPre_Ops.
Local Existing Instance ILPre_ILogic.
Local Existing Instance EmbedOpId.
Local Existing Instance EmbedId.
Local Existing Instance ILFun_Ops.
Local Existing Instance ILFun_ILogic.
Local Existing Instance SAIBIOps.
Local Existing Instance SAIBILogic.
Local Existing Instance BILPre_Ops.
Local Existing Instance IBILPreLogic.
Local Existing Instance BILFun_Ops.
Local Existing Instance IBILFunLogic.

Local Existing Instance MapSepAlgOps.
Local Existing Instance MapSepAlg.
Local Existing Instance MapEquiv.
Local Existing Instance EquivPreorder.
Local Existing Instance UUMapSepAlg.
Local Existing Instance SepAlgOps_prod.
Local Existing Instance SepAlg_prod.
Local Existing Instance UUSepAlg_prod.

Instance ILogicOpsPSasn    : ILogicOps psasn    := _.
Instance ILogicPSasn       : ILogic psasn       := _.
Instance BILOperatorsPSasn : BILOperators psasn := _.
Instance BILogicPSasn      : BILogic psasn      := _.
Instance IBILogicPSasn     : IBILogic psasn     := _.

Local Existing Instance EmbedILFunDropOp.
Local Existing Instance EmbedILFunDrop.
Local Existing Instance EmbedILFunOp.
Local Existing Instance EmbedILFun.
Local Existing Instance EmbedILPreOp.
Local Existing Instance EmbedILPre.

Local Existing Instance SABIOps.
Local Existing Instance SABILogic.
Local Existing Instance pureop_bi_sepalg.

Instance EmbedPSasnPropOp : EmbedOp Prop psasn := _.
Instance EmbedPSasnProp   : Embed Prop psasn   := _.

Instance EmbedPSasnPureOp : EmbedOp vlogic psasn := _.
Instance EmbedPSasnPure   : Embed vlogic psasn   := _.

Instance EmbedPSasnSpecOp : EmbedOp spec psasn := _.
Instance EmbedPSasnSpec   : Embed spec psasn   := _.

Instance EmbedPSasnSasnOp : EmbedOp sasn psasn := _. 
Instance EmbedPSasnSasn   : Embed sasn psasn := _.

Module IsMarshallable.
  Require Import Heap Relations RelationPairs ZArith.
  Import Marshall.
  
  Program Definition isMarshallable (v : var) (P : psasn) : psasn :=
  	fun PM STs s => mk_asn (fun Pr k h =>
    	forall m h' Pr' k' (Hsh: subheap h h') (Hsp: Prog_wf_sub Pr Pr'), 
    	marshall Pr' (s v) h' m -> P PM STs s Pr' k' m
  	) _ _ _.
  Next Obligation.
    eapply H0; try eassumption.
    transitivity P'; assumption.
  Defined.
  Next Obligation.
    eapply H0; [ | assumption | eassumption].
    transitivity h'; eassumption.
  Defined.

  Local Transparent EmbedILFunDropOp.
  Local Transparent EmbedILFunOp.
  Local Transparent EmbedAsnPropOp.
  Local Transparent RelCompFun.
  
  Local Existing Instance MapSepAlgOps.
  Local Existing Instance MapSepAlg.
  Local Existing Instance MapEquiv.
  Local Existing Instance EquivPreorder.
  Local Existing Instance UUMapSepAlg.
  Local Existing Instance SepAlgOps_prod.
  Local Existing Instance SepAlg_prod.
  Local Existing Instance UUSepAlg_prod.

  Lemma pointsto_isMarshallable_aux (p : var) (pos : nat) (cls : class) (f : field) (v : val) :
    forall PM STs (s:stack) (Pr:Prog_wf) k h fields
         (Href : s p = (vptr (pos, cls)))
      (Hfields : field_lookup Pr cls fields)
     (Hisfield : SS.In f fields)
    (Hpointsto : (pointsto (vptr (pos, cls)) f v) Pr k h), 
    (isMarshallable p (embed (pointsto (vptr (pos, cls)) f v))) PM STs s Pr k h
    .
  Proof.
    simpl. intros.
    split; [apply Hpointsto |].
    induction H; [
    	rewrite Vint in Href |
    	rewrite Vbool in Href |
    	rewrite Vptr in Href
    ]; inversion Href; subst.
    inversion H1; subst; clear H1 Href.
    exists (remove ((pos, cls), f) (get_heap_ptr m)).
    apply sa_mul_swapL; [apply sa_mulC; apply uusa_unit; apply empty_1 |].
    (* Make Hisfield talk about field0 *)
    assert (SS.Equal fields fields0) by (eapply field_lookup_function_sub; eassumption).
    rewrite H0 in Hisfield; clear H0.
    (* And then use Mhere, now that we have the field0 evidence *)
    apply Mhere; assumption.
  Qed.
    
End IsMarshallable.


