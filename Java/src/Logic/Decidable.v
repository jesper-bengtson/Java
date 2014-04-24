Require Import Program  Heap ProtocolLogic AssertionLogic OperationalSemantics SpecLogic Util.
Require Import MapInterface MapFacts.
Require Import SepAlg SepAlgInsts ILInsts ILogic ILEmbed ILEmbedTac ILQuantTac OpenILogic
               SepAlgMap UUSepAlg Open Subst Stack Lang SemCmd HeapArr ST SemCmdRules BILogic BILInsts Rel.


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
Local Transparent ILOpsSAsn.

Local Existing Instance DecSval.

Lemma pointsto_decidable (v : val) (f : field) (e : val) :
  (DecidableAsn (pointsto v f e)).
Proof.
  intros Pr n h; simpl.
  destruct (dec_eq v null) as [Hnull | Hnotnull]; [
    unfold var_expr; simpl; right; intro Hfail; destruct Hfail as [Hfail _]; rewrite Hnull in Hfail; auto |].
  destruct v;
    try (unfold var_expr; simpl; right; intro Hfail; destruct Hfail as [Hfail _]; apply Hfail; reflexivity).
  assert (p <> pnull) as Hnotpnull by (intro Hfail; apply Hnotnull; unfold null; rewrite Hfail; reflexivity).
  
  destruct (In_dec (get_heap_ptr h) (p, f)) as [Hin | Hnotin].
  destruct Hin as [k Hmapsto].
  destruct (dec_eq k e) as [Heq | Hneq]; [ subst |].
  - left; split; [assumption |].
    exists (remove (p, f) (get_heap_ptr h)).
    apply sa_mul_swapL; [apply sa_mulC; apply uusa_unit; apply empty_1 | assumption].
  - right. intro Hfail; destruct Hfail as [_ Hfail].
    apply Hneq.
    destruct Hfail as [? Hfail].
    eapply sa_mul_mapstoR in Hfail; [| apply Hmapsto].
    destruct Hfail as [[Hfail _] | [_ Hfail]].
    + apply find_mapsto_iff in Hfail. rewrite add_eq_o in Hfail; [| reflexivity].
      inversion Hfail; reflexivity.
    + exfalso; apply Hfail; exists e.
      apply add_1; reflexivity.
  - right. intros Hfail; destruct Hfail as [_ Hfail].
    apply Hnotin.
    unfold subheap in Hfail; destruct Hfail as [? Hfail].
    exists e.
    eapply sa_mul_mapstoL; [apply Hfail |].
    apply add_1; reflexivity.
Qed.

Lemma pointsto_decidable_2 (v : val) (f : field) (e : val) (Q : asn) :
  DecidableAsn Q -> DecidableAsn (Q ** pointsto v f e).
Proof.
  unfold DecidableAsn; simpl.
  intros H Pr n h; simpl.
  
  destruct (dec_eq v null) as [Hnull | Hnotnull]; [
    unfold var_expr; right; intro Hfail; destruct Hfail as [h1 [h2 [Hh [_ [HP _]]]]]; simpl in HP; rewrite Hnull in HP; auto |].
  destruct v;
    try (unfold var_expr; right; intro Hfail; destruct Hfail as [h1 [h2 [Hh [_ [HP _]]]]]; simpl in HP; apply HP; reflexivity).
  assert (p <> pnull) as Hnotpnull by (intro Hfail; apply Hnotnull; rewrite Hfail; reflexivity).
  
  specialize (H Pr n (mkheap (remove (p, f) (get_heap_ptr h)) (get_heap_arr h))).
  destruct H as [HQ | notHQ].
  * destruct (In_dec (get_heap_ptr h) (p, f)) as [Hin | Hnotin].
    destruct Hin as [k Hmapsto]. 
    destruct (dec_eq k e) as [Heq | Hneq]; [ subst |].
    - left; simpl.
      exists (mkheap (remove (p, f) (get_heap_ptr h)) (get_heap_arr h)).
      exists (mkheap (add (p, f) e (empty _)) (empty _)).
      assert (sa_mul (mkheap (remove (p, f) (get_heap_ptr h)) (get_heap_arr h)) 
                     (mkheap (add (p, f) e (empty val)) (empty val)) h) by (
        apply split_heap; simpl; [apply sa_mulC; apply sa_mul_swapL; [apply sa_mulC; apply uusa_unit; apply empty_1 | apply Hmapsto] |
      	  						  apply uusa_unit; apply empty_1]).
      exists H.
      split; [ apply HQ |].
      simpl. split; [ apply Hnotpnull |].
      exists (empty _); apply uusa_unit; apply empty_1.
    - right; simpl; intro Hfail. destruct Hfail as [h1 [h2 [Hh [_ [_ HP]]]]].
      destruct HP as [? HP]; simpl in HP.
      eapply sa_mul_mapstoL in HP; [| apply add_1; reflexivity ].
      apply sa_mulC in Hh. apply isolate_heap_ptr in Hh. eapply sa_mul_mapstoL in Hh; [| apply HP].
      destruct Hh as [Hh _].
      apply find_mapsto_iff in Hh; apply find_mapsto_iff in Hmapsto.
      rewrite Hh in Hmapsto.
      apply Hneq; inversion Hmapsto; reflexivity.
    - right. intro Hfail. destruct Hfail as [h1 [h2 [Hh [_ [_ HP]]]]].
      unfold liftn, lift, var_expr in HP; simpl in HP.
      apply Hnotin; exists e.
      destruct HP as [? HP]; simpl in HP.
      eapply sa_mul_mapstoL in HP; [| apply add_1; reflexivity ].
      apply sa_mulC in Hh. apply isolate_heap_ptr in Hh. eapply sa_mul_mapstoL in Hh; [| apply HP].
      apply Hh.
  * right.
    intro Hfail; apply notHQ.
    destruct Hfail as [h1 [h2 [Hh [HQ HP]]]].
	solve_model HQ; unfold rel.
	exists (mkheap (remove (p, f) (get_heap_ptr h2)) (get_heap_arr h2)).
	apply split_heap; simpl; [| apply Hh].
	assert (~ In (p, f) (get_heap_ptr h1)). {
	  intro Hfail.
	  unfold liftn, lift, var_expr in HP; simpl in HP.
	  destruct HP as [_ [? HP]]; simpl in HP.
	  eapply sa_mul_mapstoL in HP; [| apply add_1; reflexivity ].
	  apply isolate_heap_ptr in Hh; apply sa_mulC in Hh; eapply sa_mul_inL in Hh; [| exists e; apply HP].
	  destruct Hh as [Hh _].
	  apply Hh; apply Hfail.
    }
    apply sa_mulC.
    eapply sa_mul_remove; [ apply sa_mulC; apply Hh | apply H ].
Qed.

Lemma decidable_existsI (p : val) (f : field) (P : sval -> asn) : 
  (forall a, DecidableAsn (P a)) -> DecidableAsn ( @lexists asn _ _ (fun a => (P a)  ** pointsto p f a)). 
Proof.
  intros H Pr n h; simpl.
  destruct (dec_eq p pnull) as [Hnull | Hnotnull]; [
    right; intro Hfail; destruct Hfail as [p' [h1 [h2 [Hh [_ [Hhead _]]]]]]; simpl in Hhead; rewrite Hnull in Hhead; auto |].
  destruct p;
    try (right; intro Hfail; destruct Hfail as [p' [h1 [h2 [Hh [_ [Hhead _]]]]]]; simpl in Hhead; apply Hhead; reflexivity).
  assert (p <> pnull) as Hnotpnull by congruence.
  
  destruct (In_dec (get_heap_ptr h) (p, f)) as [[val Hin] | Hnotin].
  remember (mkheap (remove (p, f) (get_heap_ptr h)) (get_heap_arr h)) as h'.
  destruct (H val Pr n h').
  - (* success, P holds for val *)
    left.
    exists val.
    exists (mkheap (remove (p, f) (get_heap_ptr h)) (get_heap_arr h)).
    exists (mkheap (add (p, f) val (empty _)) (empty _)).
    assert (sa_mul (mkheap (remove (p, f) (get_heap_ptr h)) (get_heap_arr h)) 
                   (mkheap (add (p, f) val (empty _)) (empty _)) h). {
	  apply split_heap; simpl; [| apply uusa_unit; apply empty_1 ].
	  apply sa_mulC; eapply sa_mul_swapL; [| assumption].
	  apply sa_mulC; apply uusa_unit; apply empty_1.
	}
	exists H1.
	rewrite Heqh' in H0.
	split; [assumption |].
	simpl. split; [apply Hnotpnull |].
	exists (empty _); apply uusa_unit; apply empty_1.
  - (* failure, P doesn't hold for val *)
    right.
    intro Hfail; apply H0; clear H0.
    destruct Hfail as [val' [h1 [h2 [Hh [HP [_ Hval]]]]]].
    simpl in Hval; destruct Hval as [? Hval]; eapply sa_mul_mapstoL in Hval; [| apply add_1; reflexivity]; destruct Hval as [Hval _]; clear x.
    assert (val = val'). {
      apply sa_mulC in Hh; apply isolate_heap_ptr in Hh; eapply sa_mul_mapstoL in Hh; [| eassumption].
      destruct Hh as [Hh _].
      apply find_mapsto_iff in Hh; apply find_mapsto_iff in Hin.
      rewrite Hh in Hin. inversion Hin; reflexivity.
    }
    rewrite H0; clear H0.
    solve_model HP; [| congruence ].
    unfold rel. rewrite Heqh'.
    exists (mkheap (remove (p, f) (get_heap_ptr h2)) (get_heap_arr h2)).
    apply split_heap; simpl; [| apply Hh].
    apply sa_mulC; apply sa_mul_remove; [ apply sa_mulC; apply Hh |].
    eapply sa_mul_mapstoL; [ eapply sa_mulC; apply Hh | apply Hval ].
  - (* failure, there is no p.f in the heap *)
    right.
    intro Hfail; apply Hnotin; clear Hnotin.
    destruct Hfail as [head' [h1 [h2 [Hh [_ [_ Hval]]]]]].
    simpl in Hval; destruct Hval as [? Hval]; eapply sa_mul_mapstoL in Hval; [| apply add_1; reflexivity]; destruct Hval as [Hval _]; clear x.
    apply sa_mulC in Hh; apply isolate_heap_ptr in Hh; eapply sa_mul_inL in Hh; [| exists head'; eassumption]; apply Hh.
Qed.

Global Instance DecidableAsn_m : Proper (lequiv ==> iff) DecidableAsn.
Proof.
  intros x y Hentails; split; (intros H Pr n h; destruct (H Pr n h); [
    left; apply Hentails; apply H0 | 
    right; intro Hfail; apply H0; apply Hentails; apply Hfail]).
Defined.
