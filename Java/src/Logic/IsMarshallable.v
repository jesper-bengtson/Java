Require Import Program  Heap ProtocolLogic AssertionLogic OperationalSemantics SpecLogic Util.
Require Import MapInterface MapFacts.
Require Import SepAlg SepAlgInsts ILInsts ILogic ILEmbed ILEmbedTac ILQuantTac OpenILogic
               SepAlgMap UUSepAlg Open Subst Stack Lang SemCmd HeapArr ST SemCmdRules BILogic BILInsts.


Local Transparent ILPre_Ops.
Local Transparent ILPreFrm_pred.
Local Transparent EmbedSasnPureOp.
Local Transparent EmbedILFunOp.
Local Transparent EmbedAsnPropOp.
Local Transparent ILPre_Ops.
Local Transparent EmbedILPreDropOp.
Local Transparent EmbedILPreOp.
Local Transparent MapSepAlgOps.
Local Transparent ILFun_Ops.
Local Transparent EmbedILFunDropOp.
Local Transparent EmbedILFunOp.
Local Transparent SepAlgOps_prod.

Local Transparent EmbedILPreDropOp.
Local Transparent EmbedILFunDropOp.
Local Transparent EmbedPSasnPropOp.
Local Transparent EmbedAsnPropOp.
Local Transparent BILOperatorsPSasn.
Local Transparent BILFun_Ops.
Local Transparent BILOperatorsAsn.

Lemma pointsto_IsMarshallable (v : var) (f : field) (e : expr):
  Exists C, field_exists C f /\\ embed (@land sasn _ (v ::: C) (`pointsto v/V `f e))
  |--
  isMarshallable v (`pointsto v/V `f e). 
Proof.
  intros s PM STs Pr n h [C [Hfield [Htypeof Hpointsto]]].
  simpl in Htypeof; simpl in Hfield; simpl in Hpointsto; unfold var_expr in Hpointsto.
  unfold typeof, liftn, lift, var_expr in Htypeof; simpl in Htypeof.
  destruct Htypeof as [p [Href Hclass]].
  destruct Hfield as [fields [Hfields Hisfield]].
  destruct p as [pos cls]; simpl in Hclass; rewrite Hclass in *; clear Hclass.
    
  unfold liftn, lift, var_expr; simpl.
  intros.
  split; [apply Hpointsto |].
  induction H; [
  	rewrite Vint in Href |
   	rewrite Vbool in Href |
   	rewrite Vptr in Href
  ]; inversion Href; subst.
  inversion H1; subst; simpl; clear H1 Href.
  exists (remove ((pos, C), f) (get_heap_ptr m)).
    
  apply sa_mul_swapL; [apply sa_mulC; apply uusa_unit; apply empty_1 |].
  (* Make Hisfield talk about field0 *)
  assert (SS.Equal fields fields0) by (eapply field_lookup_function_sub; eassumption).
  rewrite H0 in Hisfield; clear H0.
  (* And then use Mhere, now that we have the field0 evidence *)
  apply Mhere; assumption.
Qed.

Lemma pointsto_IsMarshallable_2 (v : var) (f : field) (e : expr) (Q : sasn):
  Exists C, field_exists C f /\\ embed (@land sasn _ (v ::: C) (`pointsto v/V `f e)) ** isMarshallable v Q
  |--
  isMarshallable v (@land sasn _ (`pointsto v/V `f e) Q). 
Proof.
  intros s PM STs Pr n h [C [Hfield [h1 [h2 [Hcompose [[Htypeof Hpointsto] HIM]]]]]].
  simpl in Htypeof; simpl in Hfield; simpl in Hpointsto; unfold var_expr in Hpointsto.
  unfold typeof, liftn, lift, var_expr in Htypeof; simpl in Htypeof.
  unfold liftn, lift in Hpointsto; simpl in Hpointsto.
  destruct Htypeof as [p [Href Hclass]].
  destruct Hfield as [fields [Hfields Hisfield]].
  destruct p as [pos cls]; simpl in Hclass; rewrite Hclass in *; clear Hclass.
  rewrite Href in *. simpl in *.
  
  unfold liftn, lift, var_expr; simpl; unfold id.
  intros; simpl.
  (* Use the introduced info to specialize HIM with *)
  (* TODO: This needs to not use h', but something without (pos, C, f) in it) *)
  assert (subheap h2 h') by (transitivity h; [ exists h1; apply sa_mulC; assumption | assumption ]).
  specialize (HIM _ _ _ k' H0 Hsp H); clear H0.
  (* Prove that the pointer is present in the marshalling *) 
  assert (MapsTo (pos, C, f) (e s) (get_heap_ptr m)). {
    inversion H; [
      rewrite Vint in Href |
      rewrite Vbool in Href |
      rewrite Vptr in Href
    ]; inversion Href. 
    rewrite Vclass in H2; inversion H2; subst.
    assert (SS.Equal fields fields0) by (eapply field_lookup_function_sub; eassumption).
    eapply Mhere; rewrite <- H0; assumption.
  }
  (* Setup the two disjoint heaps for the goal, m1 and m2 *
  remember (mkheap (add (pos, C, f) (e s) (empty _)) (empty _)) as m1.
  remember (mkheap (remove (pos, C ,f) (get_heap_ptr m)) (get_heap_arr m)) as m2.
  assert (sa_mul m1 m2 m). {
    rewrite Heqm1, Heqm2.
    apply split_heap; simpl.
    * apply sa_mul_swapL; [apply sa_mulC; apply uusa_unit; apply empty_1 | apply H0].
    * apply sa_mulC; apply uusa_unit; apply empty_1.
  }
  exists m1; exists m2; exists H1.
  rewrite Heqm1, Heqm2.
  clear Heqm1 Heqm2 H1 m1 m2. *)
  (* And solve the two goals *)
  rewrite Href; split.
  * simpl; split; [ apply Hpointsto |].
    exists (remove (pos, C, f) (get_heap_ptr m)).
    apply sa_mul_swapL; [apply sa_mulC; apply uusa_unit; apply empty_1 | assumption].
    (*exists (empty _); apply uusa_unit; apply empty_1.*)
  * apply HIM.
Qed.

  