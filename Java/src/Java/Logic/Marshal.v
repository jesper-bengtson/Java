Require Import ILogic ILInsts ILEmbed SepAlg UUSepAlg BILogic BILInsts IBILogic SepAlgMap Maps String ZArith Rel.
Require Import RelationClasses Setoid Morphisms.
Require Import Compare_dec DecidableType DecidableTypeEx OrderedType OrderedTypeEx.
Require Import MapInterface MapFacts SetoidList.
Require Import Util Lang Program Heap AssertionLogic Stack.

Inductive pMarshal (Pr : Prog_wf) (ref : ptr) : SS.t -> heap -> heap -> Prop :=
  | pMarshal_empty : forall (big : heap) fl,
                     SS.Empty fl ->
                     pMarshal Pr ref fl big (empty _)
  | pMarshal_scalar   : forall (big m m' : heap) (f : field) (fl fl' : SS.t) (v : val),
                     ~ SS.In f fl ->
  					 isField Pr ref f ->
  					 MapsTo (ref, f) v big ->
  					 val_to_ptr v = pnull ->
  					 pMarshal Pr ref fl big m ->
  					 m' === add (ref, f) v m ->
  					 SS.Equal fl' (SS.add f fl) ->
                     pMarshal Pr ref fl' big m'
  | pMarshall_ptr :  forall (big m m' m'' m_c : heap) (f : field) (fl fl' fl_c : SS.t) (cls : class) (pos : nat),
                     ~ SS.In f fl ->
                     isField Pr ref f ->
                     MapsTo (ref, f) (vptr (pos, cls)) big ->
                     vptr (pos, cls) <> pnull ->
                     pMarshal Pr ref fl big m ->
                     field_lookup Pr cls fl_c ->
                     pMarshal Pr (pos, cls) fl_c big m_c ->
                     sa_mul m m_c m' ->
                     m'' === add (ref, f) (vptr (pos, cls)) m' ->
                     SS.Equal fl' (SS.add f fl) ->
                     pMarshal Pr ref fl' big m''
  .

Inductive Marshal (Pr : Prog_wf) (v : sval) (big : heap) : heap -> Prop :=
  | Marshal_int  : forall (z : Z)
                    (Vint : v = vint z),
    	            Marshal Pr v big (empty _)
  | Marshal_bool : forall (b : bool)
                    (Vbool : v = vbool b),
                    Marshal Pr v big (empty _)
  | Marshal_ptr  : forall (cls : class) (pos : nat) (m : heap) (fl : list field) fields
                            (Vptr : v = vptr (pos, cls))
                         (Vfields : field_lookup Pr cls fields)
                     (Vmarshaling : pMarshal Pr (pos, cls) fields big m),
                     Marshal Pr v big m
  .

Add Parametric Morphism : pMarshal with signature
  eq --> eq --> SS.Equal --> Equal --> Equal --> impl
as pMarshal_Equal_m.
Proof.
  admit (* fangel, pMarshal set Equal morphism *).
Qed. 

Add Parametric Morphism : Marshal with signature
  eq --> eq --> Equal --> Equal --> impl
as Marshal_Equal_m.
Proof.
  admit (* fangel, pMarshal set Equal morphism *).
Qed. 

Local Existing Instance DecSval.

Require Import FSets.FSetProperties.

Lemma pMarshal_field_is_in : forall Pr ptr f v' fl h h', MapsTo (ptr, f) v' h -> pMarshal Pr ptr fl h h' -> SS.In f fl -> MapsTo (ptr, f) v' h'.
Proof.
  intros Pr ptr f v' fl h h' HMT HpM HIn.
  induction HpM; subst.
  - apply SS'.empty_is_empty_1 in H; rewrite H in HIn; inversion HIn.
  - destruct (eq_dec f f0).
    + assert ((ref, f) === (ref, f0)) by (split; [ reflexivity | rewrite H5; reflexivity]). rewrite <- H6 in H1.
      replace (v') with (v) by (apply find_mapsto_iff in H1; apply find_mapsto_iff in HMT; rewrite H1 in HMT; inversion HMT; reflexivity).
      rewrite H3; apply add_1; auto. 
    + rewrite H3; apply add_2. 
      * intro Hfail; apply H5. inversion Hfail. rewrite H11; reflexivity.
      * rewrite H4 in HIn; apply SS'.add_iff in HIn; destruct HIn; [ exfalso; apply H5; rewrite H6; reflexivity |].
        apply IHHpM; assumption. 
  - destruct (eq_dec f f0).
    + assert ((ref, f) === (ref, f0)) by (split; [ reflexivity | rewrite H7; reflexivity]). rewrite <- H8 in H1.
      replace (v') with (vptr (pos, cls)) by (apply find_mapsto_iff in H1; apply find_mapsto_iff in HMT; simpl in *; rewrite H1 in HMT; inversion HMT; reflexivity).
      rewrite H5; apply add_1; auto.
    + rewrite H5; apply add_2.
      * intro Hfail; apply H7. inversion Hfail. rewrite H13; reflexivity. 
      * rewrite H6 in HIn; apply SS'.add_iff in HIn; destruct HIn; [ exfalso; apply H7; rewrite H8; reflexivity |].
        eapply sa_mul_mapstoL; [apply H4 |].
        apply IHHpM1; assumption.
Qed.

Lemma pMarshal_subheap : forall Pr v fl h h', pMarshal Pr v fl h h' -> subheap h' h.
Proof.
  intros.
  induction H; subst.
  - exists big; apply sa_mulC; apply uusa_unit; apply empty_1.
  - destruct IHpMarshal as [mh' HM].
    exists (remove (ref, f) mh').
    rewrite H4; eapply sa_mul_swapL; [ apply HM | apply H1 ].
  - assert (subheap m' big) by (eapply map_sa_mul_combined_subheap; eassumption).
    destruct H9 as [mh'' HM].
    exists (remove (ref, f) mh'').
    rewrite H7; eapply sa_mul_swapL; [ apply HM | apply H1 ].
Qed.

Lemma Marshal_subheap : forall Pr v h h', Marshal Pr v h h' -> subheap h' h.
Proof.
  intros; inversion H; [ | | eapply pMarshal_subheap; eassumption];
    exists h; apply sa_mulC; apply uusa_unit; apply empty_1.
Qed.

Lemma pMarshal_smaller_fail_aux : forall fl, (fun fl => forall Pr v v' k h m, MapsTo k v' m -> ~MapsTo k v' h -> ~ pMarshal Pr v fl h m) fl.
Proof.
  apply SS'.set_induction; intros ? ? ? ? ? ? ? ?. 
  - intros HRes HSmaller HFail; apply HSmaller; clear HSmaller.
    inversion HFail; subst; [inversion HRes | ..]; [rewrite H6 in H | rewrite H9 in H];
      apply SS'.empty_is_empty_1 in H; specialize (H f); 
      destruct H as [H _]; specialize (H (SS.add_1 _ (eq_refl _)));
      inversion H.
  - intros ? ? ? ? HRes HSmaller HFail.
    specialize (H Pr v v' k).
    apply SS'.Add_Equal in H1.
    assert (pMarshal Pr v (SS.add x s) h m) as HFail' by (rewrite <- H1; assumption); clear HFail.
    inversion HFail'; subst.
    + inversion HRes.
    + admit (* fangel, work-in-progress *).
    + admit (* fangel, work-in-progress *).
Admitted.    

Lemma Marshal_smaller_fail : forall Pr v v' k h m, MapsTo k v' m -> ~MapsTo k v' h -> ~ Marshal Pr v h m.
Proof.
  intros ? ? ? ? ? ? HRes HSmaller HFail; apply HSmaller.
  inversion HFail; subst; [ inversion HRes | inversion HRes |].
  eapply pMarshal_smaller_fail_aux in HRes; [| apply HSmaller].
  exfalso; apply HRes; apply Vmarshaling.
Qed.

Lemma Marshal_Prog_wf_sub : forall Pr Pr' v h h', Prog_wf_sub Pr Pr' -> Marshal Pr v h h' -> Marshal Pr' v h h'.
Proof.
  admit (* fangel, todo *).
Admitted.

Lemma Marshal_uc_heap : forall Pr v h h' h'', subheap h h' -> Marshal Pr v h h'' -> Marshal Pr v h' h''.
Proof.
  admit (* fangel, todo *).
Admitted.

Program Definition isMarshalable (P : asn) (v : val) : asn := mk_asn (fun Pr n h =>
  exists h', Marshal Pr v h h' /\ P Pr n h') _ _ _. 
Next Obligation.
  exists H. split; [assumption |]. solve_model H1.
Qed.
Next Obligation.
  exists H0. split.
  eapply Marshal_Prog_wf_sub; eassumption.
  solve_model H2.
Qed.
Next Obligation.
  exists H0.
  split; [| assumption].
  eapply Marshal_uc_heap; eassumption.
Qed.

Axiom Marshal_decidable : forall Pr v h, (exists h', Marshal Pr v h h') \/ (forall h', ~ Marshal Pr v h h').
Axiom Marshal_func : forall Pr v h h' h'', Marshal Pr v h h' -> Marshal Pr v h h'' -> h' === h''.

Open Scope string_scope.

(*
Definition Node_list_class : Class := Build_Class (SS.add "val" (SS.add "next" (SS.empty))) (SM.empty _).
Definition List_class : Class := Build_Class (SS.add "head" (SS.empty)) (SM.empty _).

Definition MinimalProg : Program := Build_Program (SM.add "List" List_class (SM.add "Node_list" Node_list_class (SM.empty _))).
*)

Local Transparent EmbedAsnPropOp.
Local Transparent EmbedILPreDropOp.

Lemma isField_in_fields : forall (Pr : Prog_wf) f fields pos cls, field_lookup Pr cls fields -> isField Pr (pos, cls) f -> SS.In f fields.
Proof.
  intros Pr f fields pos cls Hlookup HisField.
  unfold isField in HisField; specialize (HisField cls pos).
  destruct HisField as [field' [_ [Hlookup' HinFields]]].
  eapply field_lookup_function in Hlookup'; [| apply Hlookup]; subst.
  apply HinFields.
Qed.

(*
Definition pointsto_isM : forall v f v', isMarshalable (pointsto v f v') v.
Proof.
  intros v f v' Pr h h' n [HP HM].
  inversion HM; destruct HP as [Hnotnull [HisField Hsubheap]];
    subst; simpl in *; try (exfalso; apply Hnotnull; reflexivity).
  unfold pointsto; split; simpl; [assumption | split; [assumption |]].
  
  exists (remove ((pos, cls), f) h').
  apply sa_mul_swapL; [ apply sa_mulC; apply uusa_unit; apply empty_1 |].
 
  eapply pMarshal_field_is_in; try eassumption.
  - destruct Hsubheap as [h'' Hsubheap]; eapply sa_mul_mapstoL; [apply Hsubheap | apply add_1; reflexivity].
  - eapply isField_in_fields; eassumption.
Qed.
*)

Fixpoint Node_list (p : sval) (xs : list sval) : asn :=
  match xs with
    | nil => embed (p = null)
    | x :: xs => Exists v, pointsto p "val" x ** pointsto p "next" v ** Node_list v xs  
  end
.

Definition List_rep (p : sval) (xs : list sval) : asn :=
  Exists head, pointsto p "head" head ** Node_list head xs.

(*
Local Transparent EmbedAsnPropOp.
Local Transparent EmbedILPreDropOp.
Definition Node_list_isM : forall xs v, isMarshalable (Node_list v xs) v.
Proof.
  intros xs v.
  induction xs.
  - intros Pr h h' n [HP HM].
    apply HP.
  - intros Pr h h' n [HP HM].
    simpl in *.
    destruct HP as [next HP]; exists next.
    destruct HP as [h0 [h12 [Hsub [HPval [h1 [h2 [Hsub' [HPnext HPrec]]]]]]]].
    inversion HM; subst; try (destruct HPval as [HPval _ ]; simpl in HPval; exfalso; apply HPval; reflexivity); clear HM.
    destruct HPval as [Hptrnotnull [valIsField valMT]]; simpl in valIsField, Hptrnotnull.
    destruct valMT as [? valMT];
      eapply sa_mul_mapstoL in valMT; [| apply add_1; reflexivity]; destruct valMT as [valMT _]; clear x;
      eapply sa_mul_mapstoL in valMT; [| apply Hsub]; destruct valMT as [valMT _].
    eapply pMarshal_field_is_in in valMT; try eassumption; [| eapply isField_in_fields; eassumption]; simpl in valMT.
    destruct HPnext as [_ [nextIsField nextMT]]; simpl in nextIsField.
    destruct nextMT as [? nextMT];
      eapply sa_mul_mapstoL in nextMT; [| apply add_1; reflexivity]; destruct nextMT as [nextMT _]; clear x;
      eapply sa_mul_mapstoL in nextMT; [| apply Hsub']; destruct nextMT as [nextMT _];
      eapply sa_mul_mapstoL in nextMT; [| apply sa_mulC in Hsub; apply Hsub]; destruct nextMT as [nextMT _].
    eapply pMarshal_field_is_in in nextMT; try eassumption; [| eapply isField_in_fields; eassumption]; simpl in nextMT.
    unfold isMarshalable in IHxs.
    
    exists (add ((pos, cls), "val") a (empty _)).
    exists (remove ((pos, cls), "val") h').
    assert (sa_mul (add ((pos, cls), "val") a (empty _)) (remove ((pos, cls), "val") h') h'). {
      apply sa_mul_swapL; [apply sa_mulC; apply uusa_unit; apply empty_1 | apply valMT].
    }
    exists H; clear H.
    split; [unfold pointsto, pointsto_aux; split; [apply Hptrnotnull | simpl; split]; [apply valIsField | exists (empty _); apply uusa_unit; apply empty_1] |].
     
  admit (* fangel, work-in-progress *).
Admitted.
*)
