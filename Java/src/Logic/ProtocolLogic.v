Require Import Rel Open Later ILogic ILInsts BILogic BILInsts IBILogic SepAlg SepAlgMap
               UUSepAlg SepAlgInsts OpenILogic Pure ILEmbed PureInsts Subst Stack.
Require Import Maps MapInterface MapFacts.
Require Import Lang ST AssertionLogic SpecLogic Util Program.

Definition PM := Map [protocol, ST].

  Local Existing Instance ILPre_Ops.
  Local Existing Instance ILPre_ILogic.
  Local Existing Instance EmbedOpId.
  Local Existing Instance EmbedId.
  Local Existing Instance ILFun_Ops.
  Local Existing Instance ILFun_ILogic.
  
  Local Existing Instance ILLaterNat.
  Local Existing Instance ILLaterNatOps.
  Local Existing Instance ILLaterPre.
  Local Existing Instance ILLaterPreOps.
  Local Existing Instance ILLaterFun.
  Local Existing Instance ILLaterFunOps.
  
  Local Existing Instance SAIBIOps.
  Local Existing Instance SAIBILogic.
  Local Existing Instance BILFun_Ops.
  Local Existing Instance BILPre_Ops.
  Local Existing Instance IBILPreLogic.
  Local Existing Instance BILFun_Ops.
  Local Existing Instance BILFunLogic.
  Local Existing Instance IBILFunLogic.

  Local Existing Instance MapSepAlgOps.
  Local Existing Instance MapSepAlg.
  Local Existing Instance MapEquiv.
  Local Existing Instance EquivPreorder.
  Local Existing Instance UUMapSepAlg.
  Local Existing Instance SepAlgOps_prod.
  Local Existing Instance SepAlg_prod.
  Local Existing Instance UUSepAlg_prod.
  
  Local Existing Instance EmbedILFunDropOp.
  Local Existing Instance EmbedILFunDrop.
  Local Existing Instance EmbedILFunOp.
  Local Existing Instance EmbedILFun.
  Local Existing Instance EmbedILPreOp.
  Local Existing Instance EmbedILPre.

  Local Existing Instance SABIOps.
  Local Existing Instance SABILogic.
  Local Existing Instance pureop_bi_sepalg.

  Local Transparent ILPre_Ops.
  Local Transparent ILFun_Ops.
  Local Transparent BILPre_Ops.
  Local Transparent BILFun_Ops.

  Definition pasn := STs -> asn.
  
  Instance ILogicOpsPAsn    : ILogicOps pasn    := _.
  Instance ILogicPAsn       : ILogic pasn       := _.
  Instance BILOperatorsPAsn : BILOperators pasn := _.
  Instance BILogicPAsn      : BILogic pasn      := _.
  Instance IBILogicPAsn     : IBILogic pasn     := _.

  Instance EmbedPAsnPropOp  : EmbedOp Prop pasn := _.
  Instance EmbedPAsnProp    : Embed Prop pasn   := _.
  
  Instance EmbedPAsnSpecOp  : EmbedOp spec pasn := _.
  Instance EmbedPAsnSpec    : Embed spec pasn   := _.
  
  Instance EmbedPAsnAsnOp   : EmbedOp asn pasn  := _.
  Instance EmbedPAsnAsn     : Embed asn pasn    := _.
  
  Definition psasn := @open var _ pasn.

  Instance ILogicOpsPSasn    : ILogicOps psasn    := _.
  Instance ILogicPSasn       : ILogic psasn       := _.
  Instance BILOperatorsPSasn : BILOperators psasn := _.
  Instance BILogicPSasn      : BILogic psasn      := _.
  Instance IBILogicPSasn     : IBILogic psasn     := _.

  Instance EmbedPSasnPropOp : EmbedOp Prop psasn := _.
  Instance EmbedPSasnProp   : Embed Prop psasn   := _.

  Instance EmbedPSasnPureOp : EmbedOp vlogic psasn := _.
  Instance EmbedPSasnPure   : Embed vlogic psasn   := _.

  Instance EmbedPSasnSpecOp : EmbedOp spec psasn := _.
  Instance EmbedPSasnSpec   : Embed spec psasn   := _.

  Instance EmbedPSasnAsnOp : EmbedOp asn psasn := _. 
  Instance EmbedPSasnAsn   : Embed asn psasn := _.

  Instance EmbedPSasnSasnOp : EmbedOp sasn psasn := _. 
  Instance EmbedPSasnSasn   : Embed sasn psasn := _.
  
  Program Definition has_ST (v : var) (T : ST) : psasn :=
    fun s STs => mk_asn (fun P k h =>
      MapsTo (val_to_stptr (s v)) T STs
    ) _ _ _.

  Program Definition has_subst_ST (x z y : var) (T : ST) : psasn :=
    fun s STs => mk_asn (fun P k h =>
      MapsTo (val_to_stptr (s x)) (subst_ST z (s y) T) STs
    ) _ _ _.

  Program Definition all_STs (T : ST) : psasn :=
    fun s STs => mk_asn (fun P k h =>
      forall c, In c STs -> MapsTo c T STs
    ) _ _ _.
  
  (*
  Import Marshall.
  Program Definition isMarshallable (v : var) (P : sasn) : psasn :=
  	fun s PM STs => mk_asn (fun Pr k h =>
    	forall m h' Pr' k' (Hsh: subheap h h') (Hsp: Prog_wf_sub Pr Pr'), 
    	marshall Pr' (s v) h' m -> P s Pr' k' m
  	) _ _ _.
  Next Obligation.
    eapply H0; try eassumption.
    transitivity P'; assumption.
  Defined.
  Next Obligation.
    eapply H0; [ | assumption | eassumption].
    transitivity h'; eassumption.
  Defined.
  *)
  
  (*
  Program Definition DecidableAsn (P : sasn) : sasn := 
    fun s => mk_asn (fun Pr n h =>
     P s Pr n h \/ ~(P s Pr n h)
   ) _ _ _.
  Next Obligation.
    destruct H. left.
    solve_model H.
    right; intro Hfail; apply H. solve_model Hfail.

  Program Definition DecidableAsn (P : sasn) : sasn := 
    fun s' => mk_asn (fun Pr' n' h' =>
      forall s Pr n h, P s Pr n h \/ ~(P s Pr n h)
   ) _ _ _.
  *)
  Definition DecidableAsn (P : asn) := forall Pr n h, P Pr n h \/ ~(P Pr n h).
  Definition DecidableSasn (P : sasn) := forall s, DecidableAsn (P s).
