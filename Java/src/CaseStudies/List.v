Require Import Program  Heap ProtocolLogic AssertionLogic OperationalSemantics SpecLogic Util IsMarshallable.
Require Import MapInterface MapFacts List.
Require Import SepAlg SepAlgInsts ILInsts ILogic ILEmbed ILEmbedTac ILQuantTac OpenILogic
               SepAlgMap UUSepAlg Open Subst Stack Lang SemCmd HeapArr ST SemCmdRules BILogic BILInsts Rel.

Open Scope string_scope.

Fixpoint Node_list (p : val) (xs : list sval) : asn :=
  match xs with
    | nil => embed (p = null)
    | x :: xs => Exists v, Node_list v xs ** pointsto p "val" x ** pointsto p "next" v 
  end
.

Definition List_rep (p : val) (xs : list sval) : asn :=
  Exists head, pointsto p "head" head ** Node_list head xs.

Local Existing Instance DecSval.

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
Local Transparent EmbedAsnPropOp.
Local Transparent EmbedILPreDropOp.

Lemma Node_list_decidable (p : val) (xs : list sval) : DecidableAsn (`Node_list `p `xs).
Proof.
  unfold liftn, lift, var_expr; simpl.
  generalize dependent p.
  induction xs.
  * intros p s Pr n h.
    destruct (dec_eq p null).
    left; apply e.
    right; intro Hfail; auto.
  * intros p s Pr n h.
    destruct (dec_eq (val_to_ptr p) pnull) as [Hnull | Hnotnull]; [
      right; intro Hfail; destruct Hfail as [p' [h1 [h2 [Hh [HNodeList [h3 [h4 [Hh2 [[HPval _] _]]]]]]]]]; simpl in HPval; auto |].
    destruct p; try (right; intro Hfail; destruct Hfail as [p' [h1 [h2 [Hh [HNodeList [h3 [h4 [Hh2 [[HPval _] _]]]]]]]]]; simpl in HPval; apply HPval; reflexivity).
  
    destruct (In_dec (get_heap_ptr h) (p, "val")) as [Hinval | Hnotinval]; [destruct Hinval as [val Hinval] |].
    destruct (dec_eq a val); [subst |].
    destruct (In_dec (get_heap_ptr h) (p, "next")) as [Hinnext | Hnotinnext]; [destruct Hinnext as  [next Hinnext] |].
    specialize (IHxs next s Pr n (mkheap (remove (p, "val") (remove (p, "next") (get_heap_ptr h))) (get_heap_arr h))).
    destruct IHxs.
    - (* success, we can do the pointstos and the recursion *)
      left. 
      exists next. (* pick the value we found for next *)
      
      (* Pick the heap minus p.next and p.val for the recursion *)
      exists (mkheap (remove (p, "val") (remove (p, "next") (get_heap_ptr h))) (get_heap_arr h)).
      exists (mkheap (add (p, "val") val (add (p, "next") next (empty _))) (empty _)).
      assert (sa_mul (mkheap (remove (p, "val") (remove (p, "next") (get_heap_ptr h))) (get_heap_arr h))
                     (mkheap (add (p, "val") val (add (p, "next") next (empty Stack.val))) (empty Stack.val)) h). {
        apply split_heap; simpl; [| apply uusa_unit; apply empty_1 ].
        apply sa_mulC. apply sa_mul_swapL; [| assumption ]. apply sa_mul_swapL; [| assumption]. apply sa_mulC. apply uusa_unit; apply empty_1.
      }
      exists H0.
      split; [assumption |]. (* use the induction hypothethis to deal with the recursion *)
      
      (* Pick the relevant subheaps for p.next and p.val *)
      exists (mkheap (add (p, "val") val (empty _)) (empty _)).
      exists (mkheap (add (p, "next") next (empty _)) (empty _)).
      assert (sa_mul (mkheap (add (p, "val") val (empty Stack.val)) (empty Stack.val))
                     (mkheap (add (p, "next") next (empty Stack.val)) (empty Stack.val))
                     (mkheap (add (p, "val") val (add (p, "next") next (empty Stack.val))) (empty Stack.val))). {
         apply split_heap; simpl; [| apply uusa_unit; apply empty_1].
         eapply sa_mul_add. apply sa_mulC. apply uusa_unit; apply empty_1.
         intro Hfail.
         apply add_neq_in_iff in Hfail; [apply empty_in_iff in Hfail; apply Hfail |].
         intro Hfail'. inversion Hfail'; subst. inversion H6; subst. unfold "===", _eq in H5. 
         inversion H8; subst. inversion H10; subst. inversion H12; subst.
      }
      exists H1.
      (* Use the singleton heaps to solve the pointstos *)
      split; simpl; (split; [assumption |]); exists (empty _); apply uusa_unit; apply empty_1.
    - (* failure, we cannot do the recursion *)
      right; intro Hfail; apply H.
      destruct Hfail as [? Hfail].
      assert (next = x). {
        (* Use pointsto p.next x and MapsTo p.next next to unify x and next *)
        destruct Hfail as [h1 [h2 [Hh [HNodeList [h3 [h4 [Hh2 [_ [_ HP]]]]]]]]]; simpl in HP.
        destruct HP as [h3_ptr HP].
        eapply sa_mul_mapstoL in HP; [| apply add_1; reflexivity ].
        apply sa_mulC in Hh2; apply isolate_heap_ptr in Hh2; eapply sa_mul_mapstoL in Hh2; [| apply HP].
        apply sa_mulC in Hh; apply isolate_heap_ptr in Hh; eapply sa_mul_mapstoL in Hh; [| apply Hh2].
        destruct Hh as [Hh _].
        apply find_mapsto_iff in Hh; apply find_mapsto_iff in Hinnext.
        unfold field in Hh; unfold field in Hinnext (* Ay ay ay *).
        rewrite Hinnext in Hh. inversion Hh; reflexivity.
      }
      rewrite H0 in *.
      destruct Hfail as [h1 [h2 [Hh [HNodeList Hfail]]]].
      (* Solve using the induction hypothethis *)
      solve_model HNodeList; [unfold rel | congruence].
      (* Pick what must be the taken out to form the subheap h1 *)
      exists (mkheap (remove (p, "val") (remove (p, "next") (get_heap_ptr h2))) (get_heap_arr h2)).
      apply split_heap; simpl; [| apply Hh].
      (* Use what we know from the pointsto to show that we can remove p.val and p.next from both sides *)
      destruct Hfail as [h3 [h4 [Hh2 [[_ Hval] [_ Hnext]]]]].
      simpl in Hval; destruct Hval as [? Hval]; eapply sa_mul_mapstoL in Hval; [| apply add_1; reflexivity]; destruct Hval as [Hval _]; clear x0.
      simpl in Hnext; destruct Hnext as [? Hnext]; eapply sa_mul_mapstoL in Hnext; [| apply add_1; reflexivity]; destruct Hnext as [Hnext _]; clear x0.
      apply sa_mulC; apply sa_mul_remove; [ apply sa_mul_remove; [apply sa_mulC; apply Hh |] |].
      (* Show that p.next and p.val are infact in h2, not in h1 *)
      + apply sa_mulC in Hh2. apply isolate_heap_ptr in Hh2; eapply sa_mul_inL in Hh2; [| exists x; eassumption].
        apply sa_mulC in Hh; apply isolate_heap_ptr in Hh; eapply sa_mul_inL in Hh; [ apply Hh | apply Hh2 ]. 
      + apply isolate_heap_ptr in Hh2; eapply sa_mul_inL in Hh2; [| exists val; eassumption].
        apply sa_mulC in Hh; apply isolate_heap_ptr in Hh; eapply sa_mul_inL in Hh; [ apply Hh | apply Hh2 ].
    - (* failure, there is no next-pointer *)
      right; intro Hfail; apply Hnotinnext.
      destruct Hfail as [p' [h1 [h2 [Hh [HNodeList [h3 [h4 [Hh2 [ _ [_ Hnext]]]]]]]]]].
      simpl in Hnext; destruct Hnext as [? Hnext]; eapply sa_mul_mapstoL in Hnext; [| apply add_1; reflexivity]; destruct Hnext as [Hnext _]; clear x.
      apply sa_mulC in Hh2; apply isolate_heap_ptr in Hh2; eapply sa_mul_inL in Hh2; [| exists p'; eassumption ].
      apply sa_mulC in Hh; apply isolate_heap_ptr in Hh; eapply sa_mul_inL in Hh; [| apply Hh2]; apply Hh.
    - (* failure, the value in the list is different to the value in the heap *)
      right; intro Hfail; apply n0.
      destruct Hfail as [_ [h1 [h2 [Hh [_ [h3 [h4 [Hh2 [[_ Hval] _]]]]]]]]].
      simpl in Hval; destruct Hval as [? Hval]; eapply sa_mul_mapstoL in Hval; [| apply add_1; reflexivity]; destruct Hval as [Hval _]; clear x.
      apply isolate_heap_ptr in Hh2; eapply sa_mul_mapstoL in Hh2; [| eassumption ].
      apply sa_mulC in Hh; apply isolate_heap_ptr in Hh; eapply sa_mul_mapstoL in Hh; [| apply Hh2].
      destruct Hh as [Hmapsto _].
      apply find_mapsto_iff in Hinval; apply find_mapsto_iff in Hmapsto.
      unfold field in Hinval; unfold field in Hmapsto (* Ay ay ay *).
      rewrite Hinval in Hmapsto. inversion Hmapsto; reflexivity. 
    - (* failure, there is no value-pointer *)
      right; intro Hfail; apply Hnotinval.
      destruct Hfail as [_ [h1 [h2 [Hh [_ [h3 [h4 [Hh2 [[_ Hval] _]]]]]]]]].
      simpl in Hval; destruct Hval as [? Hval]; eapply sa_mul_mapstoL in Hval; [| apply add_1; reflexivity]; destruct Hval as [Hval _]; clear x.
      apply isolate_heap_ptr in Hh2; eapply sa_mul_inL in Hh2; [| exists a; eassumption ].
      apply sa_mulC in Hh; apply isolate_heap_ptr in Hh; eapply sa_mul_inL in Hh; [| apply Hh2]; apply Hh.
Qed.

Lemma List_rep_decidable (p : val) (xs : list sval) : DecidableAsn (`List_rep `p `xs).
Proof.
  intros s Pr n h.
  unfold liftn, lift; simpl.
  destruct (dec_eq (val_to_ptr p) pnull) as [Hnull | Hnotnull]; [
    right; intro Hfail; destruct Hfail as [p' [h1 [h2 [Hh [[Hhead _] _]]]]]; simpl in Hhead; auto |].
  destruct p;
    try (right; intro Hfail; destruct Hfail as [p' [h1 [h2 [Hh [[Hhead _] _]]]]]; simpl in Hhead; apply Hhead; reflexivity).
  
  destruct (In_dec (get_heap_ptr h) (p, "head")) as [[head Hin] | Hnotin].
  remember (mkheap (remove (p, "head") (get_heap_ptr h)) (get_heap_arr h)) as h'.
  destruct (Node_list_decidable head xs s Pr n h').
  - (* success, the node starts at `head` *)
    left.
    exists head.
    exists (mkheap (add (p, "head") head (empty _)) (empty _)).
    exists (mkheap (remove (p, "head") (get_heap_ptr h)) (get_heap_arr h)).
    assert (sa_mul (mkheap (add (p, "head") head (empty val)) (empty val))
                   (mkheap (remove (p, "head") (get_heap_ptr h)) (get_heap_arr h)) h). {
	  apply split_heap; simpl; [| apply sa_mulC; apply uusa_unit; apply empty_1 ].
	  eapply sa_mul_swapL; [| assumption].
	  apply sa_mulC; apply uusa_unit; apply empty_1.
	}
	exists H0.
	unfold liftn, lift in H; simpl in H. rewrite Heqh' in H.
	split; [| assumption].
	simpl. split; [apply Hnotnull |].
	exists (empty _); apply uusa_unit; apply empty_1.
  - (* failure, the list doesn't start at `head` *)
    right. intro Hfail; apply H; clear H.
    destruct Hfail as [head' Hfail].
    assert (head = head'). {
      destruct Hfail as [h1 [h2 [Hh [[_ Hhead] _]]]].
      simpl in Hhead; destruct Hhead as [? Hhead]; eapply sa_mul_mapstoL in Hhead; [| apply add_1; reflexivity]; destruct Hhead as [Hhead _]; clear x.
      apply isolate_heap_ptr in Hh; eapply sa_mul_mapstoL in Hh; [| apply Hhead].
      destruct Hh as [Hh _].
      apply find_mapsto_iff in Hh; apply find_mapsto_iff in Hin.
      unfold field in Hh; unfold field in Hin (* Ay ay ay *).
      rewrite Hh in Hin. inversion Hin; reflexivity.
    }
    rewrite <- H in *; clear H.
    unfold liftn, lift; simpl; rewrite Heqh'.
    destruct Hfail as [h1 [h2 [Hh [[_ Hhead] HNodeList]]]].
    simpl in Hhead; destruct Hhead as [? Hhead]; eapply sa_mul_mapstoL in Hhead; [| apply add_1; reflexivity]; destruct Hhead as [Hhead _]; clear x.
    solve_model HNodeList; [| congruence].
    unfold rel.
    exists (mkheap (remove (p, "head") (get_heap_ptr h1)) (get_heap_arr h1)).
    apply split_heap; simpl; apply sa_mulC; [| apply Hh].
    apply sa_mul_remove; [apply Hh |].
    eapply sa_mul_inL; [apply Hh | exists head; apply Hhead].
  - (* failure, p.head isn't in the heap *)
    right. intro Hfail; apply Hnotin; clear Hnotin.
    destruct Hfail as [head' [h1 [h2 [Hh [[_ Hhead] _]]]]].
    simpl in Hhead; destruct Hhead as [? Hhead]; eapply sa_mul_mapstoL in Hhead; [| apply add_1; reflexivity]; destruct Hhead as [Hhead _]; clear x.
    apply isolate_heap_ptr in Hh; eapply sa_mul_inL in Hh; [| exists head'; eassumption]; apply Hh.
Qed.
