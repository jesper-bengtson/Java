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
  Require Import Heap Relations RelationPairs.
  Import Marshall.
  
  Program Definition isMarshallable (v : var) (P : psasn) : psasn :=
  	fun PM STs s => mk_asn (fun Pr k h =>
    	forall h' Pr' k' (Hk: k' <= k) (HPr: Prog_wf_sub Pr Pr'), P PM STs s Pr' k' h' -> marshall (s v) h h'
  	) _ _ _.
  Next Obligation.
    eapply H with (k' := k').
    omega.
    apply HPr.
    solve_model H0.
  Defined.
  Next Obligation.
    eapply H0. 
    apply Hk.
    transitivity P'; eassumption.
    solve_model H1.
  Defined.
  Next Obligation.
    eapply marshall_from_smaller; [eassumption |].
    eapply H0; eassumption.
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

  Lemma pointsto_isMarshallable (p : var) (ptr : ptr) (f : field) (v : val) :
    forall PM STs (s:stack) Pr k h  
    (Href: s p = (vptr ptr)) (Hpointsto: (pointsto (vptr ptr) f v) Pr k h), 
    (isMarshallable p (embed (pointsto (vptr ptr) f v))) PM STs s Pr k h
    .
  Proof.
    admit.
    (*
    intros. 
    simpl in Hpointsto.
    
    simpl. intros.
    destruct Hpointsto as [Hnotnull Hpointsto].
    destruct H as [H'notnull H'pointsto].
    unfold subheap in H'pointsto.
    destruct H'pointsto as [h'' H'pointsto].
    
    assert (h' = heap_add_ptr (mkheap h'' (get_heap_arr h')) ptr f v). admit.
    rewrite H.
    constructor. apply Href.
    unfold subheap in Hpointsto; destruct Hpointsto as [? Hpointsto].
    eapply sa_mul_mapstoL in Hpointsto.
    apply Hpointsto.
    apply add_1. reflexivity.
    
      unfold subheap in H'pointsto.
      destruct H'pointsto as [h'' H'pointsto].
      exists (mkheap h'' (get_heap_arr h')).
      
      split. intro key. unfold heap_add_ptr, mkheap, get_heap_arr; simpl.
      simpl in H'pointsto.
      specialize (H'pointsto key).
      remember (find key (get_heap_ptr h')).
      simpl in Heqo; rewrite <- Heqo in H'pointsto.
      destruct o; unfold get_heap_ptr in Heqo; rewrite <- Heqo.
      destruct H'pointsto as [[H'pointsto _] | [H'pointsto _]].
      destruct (eq_dec key (ptr, f)).
      rewrite H in H'pointsto.
      apply map_mapsto_add_eq in H'pointsto; rewrite H'pointsto.
      rewrite add_eq_o; [| auto]. reflexivity.
      apply add_neq_mapsto_iff in H'pointsto; [| symmetry; auto].
      apply empty_mapsto_iff in H'mapsto. inversion H'mapsto.
      
      apply find_mapsto_iff in H'pointsto. rewrite H'mapsto. reflexivity.
      apply add_1; auto.
      rewrite add_neq_o; [| symmetry; auto].
      unfold sa_mul in H'pointsto. simpl in H'pointsto.
      eapply sa_mul_mapstoR in H'pointsto.
      destruct H'pointsto as [[H'mapsto _] | [H'mapsto _] ].
      
      apply add_neq_mapsto_iff in H'mapsto. apply empty_mapsto_iff in H'mapsto. inversion H'mapsto.
      symmetry; apply H.
      
      SearchAbout MapsTo empty.
      
      
    apply marshall_ptr.*)
      Admitted.

End IsMarshallable.


