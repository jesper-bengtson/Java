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

Lemma pointsto_decidable (v : var) (f : field) (e : expr) :
  (* @lentails sasn _ (@ltrue sasn _) *) (DecidableAsn (`pointsto v/V `f e)).
Proof.
  intros (*_ _ _ _ _*) s Pr n h.
  destruct (dec_eq (s v) null) as [Hnull | Hnotnull]; [
    unfold var_expr; simpl; right; intro Hfail; destruct Hfail as [Hfail _]; rewrite Hnull in Hfail; auto |].
  remember (s v) as ptr; destruct ptr;
    try (unfold var_expr; simpl; right; intro Hfail; destruct Hfail as [Hfail _]; rewrite <- Heqptr in Hfail; apply Hfail; reflexivity).
  assert (p <> pnull) as Hnotpnull by (intro Hfail; apply Hnotnull; unfold null; rewrite Hfail; reflexivity).
  unfold liftn, lift, var_expr; simpl.
  rewrite <- Heqptr in *; simpl.
  destruct (In_dec (get_heap_ptr h) (p, f)) as [Hin | Hnotin].
  destruct Hin as [k Hmapsto].
  destruct (dec_eq k (e s)) as [Heq | Hneq]; [ subst |].
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
    + exfalso; apply Hfail; exists (e s).
      apply add_1; reflexivity.
  - right. intros Hfail; destruct Hfail as [_ Hfail].
    apply Hnotin.
    unfold subheap in Hfail; destruct Hfail as [? Hfail].
    exists (e s).
    eapply sa_mul_mapstoL; [apply Hfail |].
    apply add_1; reflexivity.
Qed.

Lemma pointsto_decidable_2 (v : var) (f : field) (e : expr) (Q : sasn) :
  DecidableAsn Q -> DecidableAsn (Q ** `pointsto v/V `f e).
Proof.
  unfold DecidableAsn; simpl.
  intros (* _ _ _ _ *) H s Pr n h.
  
  destruct (dec_eq (s v) null) as [Hnull | Hnotnull]; [
    unfold var_expr; right; intro Hfail; destruct Hfail as [h1 [h2 [Hh [_ [HP _]]]]]; simpl in HP; rewrite Hnull in HP; auto |].
  remember (s v) as ptr; destruct ptr;
    try (unfold var_expr; right; intro Hfail; destruct Hfail as [h1 [h2 [Hh [_ [HP _]]]]]; simpl in HP; rewrite <- Heqptr in HP; apply HP; reflexivity).
  assert (p <> pnull) as Hnotpnull by (intro Hfail; apply Hnotnull; unfold null; rewrite Hfail; reflexivity).
  
  specialize (H s Pr n (mkheap (remove (p, f) (get_heap_ptr h)) (get_heap_arr h))).
  destruct H as [HQ | notHQ].
  * destruct (In_dec (get_heap_ptr h) (p, f)) as [Hin | Hnotin].
    destruct Hin as [k Hmapsto]. 
    destruct (dec_eq k (e s)) as [Heq | Hneq]; [ subst |].
    - left.
      exists (mkheap (remove (p, f) (get_heap_ptr h)) (get_heap_arr h)).
      exists (mkheap (add (p, f) (e s) (empty _)) (empty _)).
      assert (sa_mul (mkheap (remove (p, f) (get_heap_ptr h)) (get_heap_arr h)) 
                     (mkheap (add (p, f) (e s) (empty val)) (empty val)) h) by (
        apply split_heap; simpl; [apply sa_mulC; apply sa_mul_swapL; [apply sa_mulC; apply uusa_unit; apply empty_1 | apply Hmapsto] |
      	  						  apply uusa_unit; apply empty_1]).
      exists H.
      split; [ apply HQ |].
      unfold liftn, lift, var_expr; simpl.
      rewrite <- Heqptr; simpl. split; [ apply Hnotpnull |].
      exists (empty _); apply uusa_unit; apply empty_1.
    - right; intro Hfail. destruct Hfail as [h1 [h2 [Hh [_ [_ HP]]]]].
      unfold liftn, lift, var_expr in HP; simpl in HP.
      destruct HP as [? HP].
      rewrite <- Heqptr in HP; simpl in HP.
      eapply sa_mul_mapstoL in HP; [| apply add_1; reflexivity ].
      apply sa_mulC in Hh. apply isolate_heap_ptr in Hh. eapply sa_mul_mapstoL in Hh; [| apply HP].
      destruct Hh as [Hh _].
      apply find_mapsto_iff in Hh; apply find_mapsto_iff in Hmapsto.
      rewrite Hh in Hmapsto.
      apply Hneq; inversion Hmapsto; reflexivity.
    - right. intro Hfail. destruct Hfail as [h1 [h2 [Hh [_ [_ HP]]]]].
      unfold liftn, lift, var_expr in HP; simpl in HP.
      apply Hnotin; exists (e s).
      destruct HP as [? HP].
      rewrite <- Heqptr in HP; simpl in HP.
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
	  destruct HP as [_ [? HP]].
	  rewrite <- Heqptr in HP; simpl in HP.
	  eapply sa_mul_mapstoL in HP; [| apply add_1; reflexivity ].
	  apply isolate_heap_ptr in Hh; apply sa_mulC in Hh; eapply sa_mul_inL in Hh; [| exists (e s); apply HP].
	  destruct Hh as [Hh _].
	  apply Hh; apply Hfail.
    }
    apply sa_mulC.
    eapply sa_mul_remove; [ apply sa_mulC; apply Hh | apply H ].
Qed.

Lemma exists_decidable {A : Type} (P : A -> sasn) (a : A) : DecidableAsn( P a ) -> DecidableAsn( Exists a, P a). 
Proof.
  intro H.
  intros s Pr n h.
  specialize (H s Pr n h).
  destruct H as [H | notH].
  left.
  exists a; assumption.
  right.
  intro Hfail.
  destruct Hfail as [? Hfail].
  admit (* fangel, ununsed *).
Admitted.  