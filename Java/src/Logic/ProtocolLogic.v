Require Import Rel Open ILogic ILInsts BILogic BILInsts IBILogic SepAlg SepAlgMap
               UUSepAlg SepAlgInsts OpenILogic Pure ILEmbed PureInsts Subst Stack.
Require Import Maps MapInterface MapFacts.
Require Import Lang ST AssertionLogic SpecLogic Util Program.

Definition PM := Map [protocol, @open var _ ST].

Definition psasn := PM -> sasn.

Local Transparent ILPre_Ops.
Local Transparent ILFun_Ops.
Local Transparent BILPre_Ops.
Local Transparent BILFun_Ops.

Program Definition psasn_subst (P : psasn) (sub : subst) : psasn := 
  fun PM s => mk_tasn (fun trs => mk_asn (fun Pr k h => P PM (stack_subst s sub) trs Pr k h) _ _ _) _.
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
Next Obligation.
  solve_model H0.
  congruence.
Defined.

Program Definition ST_exists (p : protocol) (T : open ST) : psasn :=
  fun PM s => mk_tasn (fun trs => mk_asn (fun P k h =>
    MapsTo p T PM
  ) _ _ _) _.

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
