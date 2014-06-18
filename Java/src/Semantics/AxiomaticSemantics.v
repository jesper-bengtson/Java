Add Rec LoadPath "/Users/jebe/git/Java/Java/bin".
Add Rec LoadPath "/Users/jebe/git/Charge/Charge!/bin".
Add Rec LoadPath "/Users/jebe/coq/user-contrib/Containers" as Containers.

Require Import Morphisms Setoid Rel.
Require Import ILogic ILInsts BILInsts ILEmbed Later SepAlgMap BILogic.
Require Import SpecLogic Pure OpenILogic AssertionLogic Program Open Stack Subst.
Require Import OperationalSemantics Lang IBILogic.
Require Import MapInterface MapFacts SemCmd SemCmdRules.
Require Import String List Omega.

Set Implicit Arguments.
Unset Strict Implicit.

Lemma rule_seq_ax c1 c2 (P Q R : sasn) :
  ({[P]} c1 {[Q]} //\\ {[Q]} c2 {[R]}) |-- {[P]} cseq c1 c2 {[R]}.
Proof.
  admit.
(*
  unfold triple. apply lforallR; intro sc. apply lpropimplR; intro Hsem.
  inversion Hsem; subst.
  
  apply lforallL with sc1; apply lforallL with sc2. lpropimplL; [apply HL | apply HR|].
  apply @seq_rule.
*)
Qed.


Lemma rule_seq c1 c2 (P Q R : sasn) G
      (Hc1 : G |-- {[P]} c1 {[Q]})
      (Hc2 : G |-- {[Q]} c2 {[R]}) :
  G |-- {[P]} cseq c1 c2 {[R]}.
Proof.
  intros; rewrite <- rule_seq_ax; apply landR; eassumption.
Qed.

Lemma rule_if_ax (e : dexpr) c1 c2 (P Q : sasn) :
  @lentails spec _
            (@land spec _ ({[@lembedand vlogic sasn _ _ (vlogic_eval e) P]} c1 {[Q]})
                   ({[@lembedand vlogic sasn _ _ (vlogic_eval (E_not e)) P]} c2 {[Q]}))
            ({[P]} cif e c1 c2 {[Q]}).
Proof.
  admit.
(*
  unfold triple. lforallR sc. apply lpropimplR; intro Hsem.
  inversion Hsem; subst. 
  lforallL scl scr. lpropimplL; [apply HL | apply HR|].
  rewrite <- @nondet_rule, <- @seq_rule, <- @seq_rule, <- @assume_rule, <- @assume_rule.
  repeat (apply landR); [apply ltrueR | apply landL1 | apply ltrueR | apply landL2];
  reflexivity.
*)
Qed.

Lemma rule_if (e : dexpr) c1 c2 (P Q : sasn) G
      (Hc1 : G |-- {[@lembedand vlogic sasn _ _ (vlogic_eval e) P]} c1 {[Q]})
      (Hc2 : G |-- {[@lembedand vlogic sasn _ _ (vlogic_eval (E_not e)) P]} c2 {[Q]}) :
  G |-- {[P]} cif e c1 c2 {[Q]}.
Proof.
  intros; rewrite <- rule_if_ax; apply landR; assumption.
Qed.

Lemma rule_while_ax (e : dexpr) c (P : sasn) :
  {[@lembedand vlogic sasn _ _ (vlogic_eval e) P]} c {[P]} |--
  {[P]} cwhile e c {[@lembedand vlogic sasn _ _ (vlogic_eval (E_not e)) P]}.
Proof.
  unfold triple. apply lforallR; intro sc. apply lpropimplR. intro Hsem.
  inversion Hsem; subst.
  apply lforallL with sc0. apply lpropimplL; [assumption|].
  rewrite <- @seq_rule; apply landR; [
    rewrite <- @kleene_rule, <- @seq_rule, <- @assume_rule; apply landR;
    [apply ltrueR | reflexivity] |
    etransitivity; [apply ltrueR | apply @assume_rule]
  ].
Qed.
  
Lemma rule_while (e : dexpr) c (P : sasn) G
      (Hc : G |-- {[@lembedand vlogic sasn _ _ (vlogic_eval e) P]} c {[P]}) :
  G |-- {[P]} cwhile e c {[@lembedand vlogic sasn _ _ (vlogic_eval (E_not e)) P]}.
Proof.
  intros; rewrite <- rule_while_ax; assumption.
Qed.

Lemma rule_assert (e : dexpr) P G
      (HPe : P |-- embed(vlogic_eval e)) :
  G |-- {[ P ]} cassert e {[ P ]}.
Proof.
  unfold triple. apply lforallR; intro sc. apply lpropimplR; intro Hsem.
  inversion Hsem; subst.
  rewrite <- assert_rule; [apply ltrueR | apply HPe]. 
Qed.

Lemma rule_skip_ax P : |-- {[P]} cskip {[P]}.
Proof.
  unfold triple. apply lforallR; intro sc. apply lpropimplR; intro Hsem.
  inversion Hsem; subst. apply @skip_rule.
Qed.

Lemma rule_skip P G : G |-- {[P]} cskip {[P]}.
Proof.
  etransitivity.
  + apply ltrueR.
  + apply rule_skip_ax.
Qed.

Require Import SepAlgInsts.
	
Local Transparent ILPre_Ops.
Local Transparent EmbedSasnPureOp.
Local Transparent EmbedILFunOp.
Local Transparent EmbedAsnPropOp.
Local Transparent ILPre_Ops.
Local Transparent BILPre_Ops.
Local Transparent BILFun_Ops.
Local Transparent EmbedILPreDropOp.
Local Transparent EmbedILPreOp.
Local Transparent MapSepAlgOps.
Local Transparent ILFun_Ops.
Local Transparent EmbedILFunDropOp.
Local Transparent EmbedILFunOp.
Local Transparent SepAlgOps_prod.

  Lemma rule_read_fwd (x y : var) (f : field) (e : expr) (P : sasn)
    (HPT : P |-- `pointsto y/V `f e) :
   @ltrue spec _ |-- {[ P ]} cread x y f {[ Exists v : val, @lembedand vlogic sasn _ _ (open_eq (x /V) (e [{`v//x}])) (P[{`v//x}])]}.
  Proof.
    unfold triple in *; intros. apply lforallR; intro sc. apply lpropimplR; intros Hsem.
    inversion Hsem; subst.
    unfold sem_triple; simpl; split; intros.
    + intro HFail; inversion HFail; subst. apply Snotin; clear Snotin HFail.
      specialize (HPT _ _ _ _ H3); unfold pointsto in HPT;
        simpl in HPT; destruct HPT as [Hnull [h'' HPT]].
        specialize (HPT (ref, f)). unfold var_expr in HPT. rewrite Sref in HPT.
        unfold liftn, lift in HPT; simpl in HPT.
        remember (@MapInterface.find (ptr * field) _ _ sval (ref, f) h0) as o.
	    destruct o; [destruct HPT as [[HPT HIn] | [Hm HPT]] | destruct HPT as [HPT _]].
        * rewrite in_find_iff. unfold val; simpl. rewrite <- Heqo.
           (* TODO : Unification fails because it can't figure out the coercion to val. This must currently be done manually, which is unintuitive as implicit arguments hide these completely. *)
           intuition congruence.
        * rewrite add_in_iff in HPT. assert False as HFalse 
        	by (apply HPT; left; reflexivity); destruct HFalse.
        * rewrite add_in_iff in HPT. assert False as HFalse 
        	by (apply HPT; left; reflexivity); destruct HFalse.
    + inversion H4; subst.
      inversion H4; subst.
      exists (s x).
      unfold open_eq.
      do 2 rewrite subst1_stack_add, subst1_val, subst_identity.
      split.
      * specialize (HPT _ _ _ _ H3); simpl in HPT.        
        destruct HPT as [H' [h'' HPT]].
        unfold var_expr; rewrite stack_lookup_add.
        unfold var_expr, liftn, lift in HPT; simpl in HPT.
        apply stack_add_val_eq in H6. subst.
        destruct h'; simpl in *.
        specialize (HPT (ref, f)). remember (MapInterface.find (ref, f) h) as o.
	    destruct o; [destruct HPT as [[HPT HIn] | [Hm HPT]] | destruct HPT as [HPT _]].
        - rewrite add_mapsto_iff in HPT. destruct HPT as [[Heq HPT] | [Hneq HPT]]. 
          rewrite Rref0 in Heq. simpl in Heq.
          rewrite <- HPT in Heqo. rewrite find_mapsto_iff in Rmaps.
          unfold val in Heqo, Rmaps; simpl in *.
          rewrite Rmaps in Heqo. inversion Heqo. reflexivity.
          assert False as HFalse. apply Hneq. rewrite Rref. reflexivity.
          destruct HFalse.
        - rewrite add_in_iff in HPT. assert False as HFalse
          	by (apply HPT; left; rewrite Rref; reflexivity); destruct HFalse.
        - rewrite add_in_iff in HPT. assert False as HFalse
          	by (apply HPT; left; rewrite Rref; reflexivity); destruct HFalse.
      * solve_model H3.
  Qed.

Require Import HeapArr.

  Lemma arr_read_fwd (x y : var) (es : list dexpr) (P : sasn) (e : expr)
        (HP : P |-- `pointsto_arr_element_aux y/V (fun s => List.map (fun e => eval e s) es) e) :
        @ltrue spec _ |-- {[ P ]} carrread x y es  {[ Exists v : val, @lembedand vlogic sasn _ _ (open_eq (x /V) (e [{`v//x}])) (P[{`v//x}])]}.
  Proof.
    unfold triple in *; intros. apply lforallR; intro sc. apply lpropimplR; intros Hsem.
    inversion Hsem; subst.
    unfold sem_triple; simpl; split; intros. clear H.
    + intro HFail; inversion HFail; subst. apply Sarr; clear Sarr HFail.
      specialize (HP _ _ _ _ H3); unfold pointsto_arr in HP;
        simpl in HP; destruct HP as [h' [Hsub HP]].
      unfold var_expr in HP; simpl in HP. rewrite Sref in *.
      destruct h, h' in *; simpl in *. apply subheap_prod in Hsub as [Hsub1 Hsub2].
      eapply find_heap_arr_subheap in HP; [|eapply Hsub2].
      exists (e s). 
      assert (val_to_nat arr = arr) by admit.
      rewrite H in HP. apply HP.
    + inversion H4; subst.
      exists (s x).
      unfold open_eq.
      do 2 rewrite subst1_stack_add, subst1_val, subst_identity.
      split.
      * specialize (HP _ _ _ _ H3); simpl in HP.        
        destruct HP as [h' [Hh HP]].
        unfold var_expr; rewrite stack_lookup_add.
        unfold var_expr in HP; simpl in HP.
        rewrite Sref in HP. simpl in *.
        destruct h'; simpl in *.
        apply subheap_prod in Hh as [Hh1 Hh2].
        eapply find_heap_arr_subheap in HP; [|eassumption].
        assert (val_to_nat arr = arr) by admit.
        rewrite H5 in HP. rewrite HP in Sfind.
        inversion Sfind. reflexivity.
      * solve_model H3.
  Qed.

  Lemma rule_write (x : var) (f : field) (e : expr) (e' : dexpr) :
    (@ltrue spec _ |-- {[ `pointsto x/V `f e ]} cwrite x f e' {[ `pointsto x/V `f (eval e')]}).
  Proof.
    unfold triple in *; intros. apply lforallR; intro sc. apply lpropimplR; intros Hsem.
    inversion Hsem; subst.
    unfold sem_triple; simpl; split; intros; destruct H3 as [H3 H5]. clear H.
    + intros Hsafe.
      inversion Hsafe; subst. simpl in *.
      unfold var_expr in *. rewrite Sref in *. simpl in *.
      unfold liftn, lift in *; simpl in *.
      apply Sin.
      destruct H5 as [h' H5].
      apply (@sa_mul_inL _ _ _ _ _ _ _ _ (ref, f)) in H5 as [_ H6]; [apply H6|].
      rewrite add_in_iff; left; reflexivity.
    + inversion H4; subst; split; [apply H3|].
      simpl in *.
      unfold liftn, lift, var_expr in *; simpl in *.
      rewrite Sref in *. simpl in *.
      assert (add (ref, f) (eval e' s') (empty sval) ===
              add (ref, f) (eval e' s') (add (ref, f) (e s') (empty sval))). {
        unfold Equivalence.equiv, Equal. intros.
        destruct (eq_dec y (ref, f)).
        + symmetry in H6; do 2 (rewrite add_eq_o; [|apply H6]); reflexivity.
        + do 3 (rewrite add_neq_o; [|intros Hfail; symmetry in Hfail; apply H6; apply Hfail]);
          reflexivity.
      }
      unfold val in *; simpl in *.
      rewrite H6.

      apply subheap_add; [apply H5|].
      rewrite add_in_iff; left; reflexivity.
  Qed.

  Lemma subst_fresh0 (vs: var -> val) :
    subst_fresh vs nil === subst0.
  Proof. reflexivity. Qed.
  Hint Rewrite subst_fresh0 : open.

  Lemma rule_write_frame G (P Q : sasn) (x : var) (f : field) (e : expr) (e' : dexpr)
        (H : P |-- Q ** `pointsto x/V `f e) :
    @lentails spec _ G ({[ P ]} cwrite x f e' {[ Q ** `pointsto x/V `f (eval e')]}).
  Proof.
    rewrite H.
    eapply roc; [rewrite sepSPC; reflexivity | rewrite sepSPC; reflexivity|].
    eapply roc_post. eapply rule_frame.
    transitivity (@ltrue spec _); [apply ltrueR|].
    eapply rule_write.
    unfold subst_mod_asn.
    rewrite sepSPC; etransitivity; [|rewrite sepSPC; reflexivity].
    apply bilsep. apply lexistsL; intro vs. reflexivity.
  Qed.

 (*
  Lemma arr_write (x : var) (e : dexpr) (e1 e2 : @open var _ val) (e' : dexpr) (vs : list val) :
        @ltrue spec _ |-- {[ `pointsto_arr x/V e1 e2 `vs ]} carrwrite x (e::nil) e' {[ `pointsto_arr x/V e1 e2 (`update `vs (`val_to_nat (eval e)) (eval e'))]}.
    unfold triple in *; intros. lforallR sc. apply lpropimplR; intros Hsem.
    inversion Hsem; subst.
    unfold sem_triple; simpl; split; intros; destruct H3 as [[H3 H5] H6].
    + intros Hsafe.
      inversion Hsafe; subst.
      unfold var_expr, liftn, lift in *; simpl in *; rewrite Sref in *.
      apply Sin; clear Sin.
      destruct h; simpl in *.
      induction vs; simpl in *. omega.
      destruct [H6
      unfold in_heap_arr.
      unfold pointsto_arr_aux in H6.
      apply subheap_prod in H3 as [H3 H4].
      eapply find_heap_arr_subheap in H5; [|eassumption].
      exists (e s). 
      assert (val_to_nat arr = arr) by admit; rewrite <- H.
      apply H5.


  Lemma arr_write (x : var) (e : expr) (e' ei : dexpr) :
        @ltrue spec _ |-- {[ `pointsto_arr_element_aux x/V (`cons (eval ei) `nil)  e ]} carrwrite x (ei::nil) e' {[ `pointsto_arr_element_aux x/V (`cons (eval ei) `nil) (eval e') ]}.
    unfold triple in *; intros. lforallR sc. apply lpropimplR; intros Hsem.
    inversion Hsem; subst.
    unfold sem_triple; simpl; split; intros; destruct H3 as [h'' [H3 H5]]. clear H.
    + intros Hsafe.
      inversion Hsafe; subst.
      unfold var_expr in *. rewrite Sref in *.
      apply Sin; clear Sin.
      destruct h, h''; simpl in *.
      apply subheap_prod in H3 as [H3 H4].
      exists (e s). simpl.
      assert (val_to_nat arr = arr) by admit; rewrite <- H.
      destruct H4 as [h''' H4].
      rewrite <- find_mapsto_iff in H5.
      eapply sa_mul_mapstoL in H5 as [H5 _]; [|eassumption].
      rewrite <- find_mapsto_iff. apply H5.
    + inversion H4; subst; destruct h''; simpl in *.
      apply subheap_prod in H3 as [H3 H6].
      unfold liftn, lift, var_expr in *; simpl in *.
      exists (hp, ha').
      split; [reflexivity|].
      simpl. rewrite Sref.
      assert (val_to_nat arr = arr) by admit. rewrite H7.
      rewrite Sref, H7 in H5. 
      inversion Sha; clear Sha.
      rewrite <- find_mapsto_iff. 
      rewrite add_mapsto_iff. left.
      split; reflexivity.
  Qed.
*)
  Implicit Arguments rule_write_frame [[P] [Q] [x] [f] [e] [e']].

  Lemma substl_trunc_add x x' v (xs : list var) ys (s: stack) :
    ~ List.In x xs ->
    List.length ys = List.length xs ->
    (substl_trunc (zip ys (List.map var_expr xs)) x') (stack_add x v s) =
    (substl_trunc (zip ys (List.map var_expr xs)) x') s.
  Proof.
    intros HnotIn Hlength. revert dependent ys.
    induction xs as [|xh xs]; intros.
    + destruct ys; [|discriminate].
      reflexivity.
    + destruct ys as [|yh ys]; [discriminate|].
      simpl. destruct (string_dec x' yh).
      * simpl. unfold var_expr. apply stack_lookup_add2. intro Hxxh. apply HnotIn.
        constructor. auto.
      * apply IHxs.
        - contradict HnotIn. simpl. auto.
        - inversion Hlength. reflexivity.
  Qed.

Require Import FunctionalExtensionality.

Lemma substl_trunc_subst
      ps ps' es (s : stack)
      (HND0  : NoDup ps')
      (HLen  : length ps = length ps')
      (HLen0 : length ps' = length es) :
	stack_subst s
      (substl_trunc (zip ps (map (fun e s => eval e s) es))) =
	stack_subst (create_stack ps' (eval_exprs s es))
	  (substl_trunc (zip ps (map var_expr ps'))).
Proof.
	apply functional_extensionality; intro x; unfold stack_subst.
	revert dependent ps'; revert dependent es.
	induction ps as [|p]; intros.
	+ destruct ps'; [|discriminate].
	  destruct es; [|discriminate].
	  reflexivity.
	+ destruct ps' as [|p']; [discriminate|].
	  destruct es as [|e]; [discriminate|].
	  simpl. destruct (string_dec x p).
	  * unfold var_expr; simpl; autorewrite with stack; reflexivity.
      * etransitivity; [apply IHps with (ps':=ps')|].
        - inversion HND0. assumption.
        - inversion HLen. reflexivity.
        - inversion HLen0. reflexivity.
        - rewrite substl_trunc_add. reflexivity.
          inversion HND0. assumption.
          inversion HLen. reflexivity.
Qed.

  Lemma call_pre_lemma
      ps ps' es (s : stack)
      (HND0  : NoDup ps')
      (HLen  : length ps = length ps')
      (HLen0 : length ps' = length es) :
    stack_subst (zip ps' es :@: s +:+ stack_empty)
      (substl_trunc (zip ps (map var_expr ps'))) =
    stack_subst s (substl_trunc (zip ps es)).
  Proof.
    apply functional_extensionality.
    intro x. unfold stack_subst.
    revert dependent ps'. revert dependent es.
    induction ps as [|p]; intros.
    + destruct ps'; [|discriminate].
      destruct es; [|discriminate].
      reflexivity.
    + destruct ps' as [|p']; [discriminate|].
      destruct es as [|e]; [discriminate|].
      simpl. destruct (string_dec x p).
      * unfold var_expr. simpl. autorewrite with stack. reflexivity.
      * etransitivity; [|apply IHps with (ps':=ps')].
        - apply substl_trunc_add.
          inversion HND0. assumption.
          inversion HLen. apply H0. 
        - inversion HND0. assumption.
        - inversion HLen. reflexivity.
        - inversion HLen0. reflexivity.
  Qed.

  Lemma call_post_stackchange (s s': stack) ps ps' x' :
    (forall p', In p' ps' -> s p' = s' p') ->
    (substl_trunc (zip ps (map var_expr ps')) x') s' =
    (substl_trunc (zip ps (map var_expr ps')) x') s.
  Proof.
    intro H. revert dependent ps'. induction ps; intros.
    + simpl. destruct (map var_expr ps'); reflexivity.
    + destruct ps' as [|p']; [reflexivity|].
      simpl. destruct (string_dec x' a).
      * simpl. symmetry. apply H. auto with datatypes.
      * apply IHps. auto with datatypes.
  Qed.
 
  Lemma rule_call_sem (C : class) (m : method) (ps : list var) (r x : var) (P Q : sasn) (es : list dexpr) c sc
    (CC : @open _ class) (T : sasn)
    (HSem : semantics c sc)
    (HEnt :  forall PP s h n, (T s PP h n) -> (open_eq CC `C) s)
    (HLen : length ps = length es) :
    |> (C :.: m |-> ps {{ P }}-{{ r, Q}}) |-- @lforall spec _ _ (fun v : val => 
      {{@lembedand vlogic sasn _ _ (open_eq (x/V) (`v)) (P //! zip ps (map (fun e s => eval e s) es) //\\ T)}}
      (call_cmd x CC m es c sc)
      {{Q //! zip (r :: ps) (((x/V):expr) :: map (fun e => e[{`v // x}]) (map (fun e s => eval e s) es))}}).
  Proof.
  	apply lforallR; intro v.
  	intros p n H p2 m' k s h Hsub Hm'n Hkm' [Hh [HP HT]].
  	specialize (HEnt _ _ _ _ HT). unfold open_eq, liftn, lift in HEnt. simpl in HEnt.
  	destruct n; simpl in *.
  	
  	(* No fuel *) {
   	assert (k = 0) by omega; subst. split.
   	+ apply OperationalSemantics.call_cmd_obligation_1.
   	+ intros h' s' HCS; inversion HCS.
    }
    (* There is fuel *)
	specialize (H n). assert (n < S n) as Hn by omega; specialize (H Hn).
	destruct H as [Hemb [args [bd [mr [XXX HOK]]]]].
	destruct (XXX _ Hsub) as [HML [HLen0 HNIn]]; clear XXX. split.
	unfold open_eq, var_expr, liftn, lift in Hh; simpl in Hh.

    (* safety *)
    + intro HFail. inversion HFail; subst.
      * contradiction (HLFail _ HML).
      * assert (HR := method_lookup_function HML HLookup).
        injection HR; intros; subst; clear HR HLookup.
        edestruct HOK with (x := sc) (x2 := m' - 1) (k := n0) (h := h) 
        (s := (create_stack ps0 (eval_exprs s es))) as [HSafe _]; 
        	[eassumption | omega | assumption | reflexivity | reflexivity | omega | |
        	 apply HSafe; apply HFail0].
	     unfold apply_subst in *.
	    solve_model HP.
        erewrite <- substl_trunc_subst; [reflexivity|..]. 
        apply prog_wf in HML. apply HML.
        assumption. assumption. 
      * assert (HT' := method_lookup_function HML HLookup); injection HT'; intros;
        subst; congruence.
    +  
    (* correctness *)
    intros h' s' HSem1; inversion HSem1; subst; clear HSem1.
    assert (HPS := method_lookup_function HLookup HML);
      inversion HPS; subst; clear HPS HLookup.
    edestruct HOK with (x := sc) (x2:=m'-1) (k:=n0) (h:=h) 
    (s := (create_stack args (eval_exprs s es))) as [_ HC];
    	clear HOK; [eassumption | omega | assumption | reflexivity | reflexivity | omega | ..].
    unfold apply_subst in *.
    solve_model HP.
    unfold apply_subst. erewrite substl_trunc_subst.
    reflexivity.
    apply prog_wf in HML. apply HML. apply HLen0. omega. 
    unfold apply_subst in *.
    specialize (HC _ _ HSem0).
    solve_model HC.
    (* equality of post stack *)
    apply functional_extensionality. intros z. unfold stack_subst. simpl. destruct (string_dec z r).
    * case (string_dec z r); [intros |congruence]. 
      unfold var_expr. rewrite stack_lookup_add. reflexivity.
    * case (string_dec z r); [congruence|intros].
      
    rewrite call_post_stackchange with (s:= create_stack args (eval_exprs s es)).
    - apply prog_wf in HML. simpl in HML.
      clear - HML HLen HLen0. revert dependent args. revert dependent es.
      { induction ps as [|p]; intros.
      + destruct es; [|discriminate].
        destruct args; [|discriminate].
        reflexivity.
      + destruct es as [|e]; [discriminate|].
        destruct args as [|p']; [discriminate|].
        simpl. destruct (string_dec z p).
        * subst p. do 2 (case (string_dec z z); [intro|congruence]). 
          unfold var_expr. simpl. autorewrite with stack. simpl.
          unfold subst1, liftn, var_expr. simpl.
          unfold eval. f_equal.
          apply functional_extensionality. intros. simpl.
          case (string_dec x0 x). intros. simpl.
          unfold lift. subst. admit. intros.
          rewrite stack_lookup_add2. reflexivity. intuition.
        * do 2 (case (string_dec z p); [congruence|intro]). 
          rewrite substl_trunc_add. apply IHps. simpl in *. omega. simpl in *. omega.
          inversion HML. assumption. inversion HML. assumption.
          simpl in *. inversion HLen0. reflexivity.
      }
    - intros p' HIn. pose modifies_syn_sem as Hmod.
      unfold c_not_modifies, not_modifies in Hmod. eapply Hmod; [| eassumption|].
      auto. apply HSem0.
 Qed.

  Lemma rule_call_static C m ps (es : list dexpr) (x r : var) P Q
    (HLen : length ps = length es) :
    |> (C :.: m |-> ps {{ P }}-{{ r, Q }}) |-- @lforall spec _ _ (fun v : val =>
      {[ @lembedand vlogic sasn _ _ (open_eq (x /V) (`v)) (P //! zip ps (map (fun e s => eval e s) es)) ]} cscall x C m es
      {[Q //! zip (r :: ps) ((x/V) :: map (fun e => e[{`v//x}]) (map (fun e s => eval e s) es))]}).
  Proof.
  	unfold triple. apply lforallR; intro v; apply lforallR; intro sc. apply lpropimplR; intro HSem.
  	inversion HSem; subst. clear HSem.
  	rewrite rule_call_sem with (T := ltrue) (x := x); [|eassumption | reflexivity | eassumption].
  	apply lforallL with v. apply rule_of_consequence. 
  	+ unfold lembedand. rewrite <- landA. apply landR; [reflexivity|apply ltrueR].
  	+ reflexivity.
  Qed.

  Lemma rule_call_dynamic C m ps (es : list dexpr) (x y r : var) P Q
    (HLen : length ps = length ((E_var y) :: es)) :
    (|> (C :.: m |-> ps {{ P }}-{{ r, Q}}) |-- @lforall spec _ _ (fun v:val =>
      {[ @lembedand vlogic sasn _ _ (@land vlogic _ (open_eq (x /V) (`v)) (`typeof `C y/V)) (P //! zip ps (map (fun e s => eval e s) ((E_var y) ::es))) ]}
      cdcall x y m es
      {[Q //! zip (r :: ps)
        ((x/V) :: (y/V) [{`v // x}] :: map (fun e => e[{`v//x}]) (map (fun e s => eval e s) es)) ]})).
  Proof.
  	unfold triple. apply lforallR; intro v; apply lforallR; intro sc. apply lpropimplR; intro HSem.
  	inversion HSem; subst. clear HSem.
  	rewrite rule_call_sem with (x := x) (CC := (fun s => val_class (y/V s))) 
                                            (T := @embed vlogic _ _ ((fun s => typeof C (y/V s))));
  		 [|eassumption | | eassumption].
    + apply lforallL with v. apply rule_of_consequence. 
      * unfold lembedand. rewrite <- embedland.
        rewrite landA, (landC _ (@embed vlogic _ _ (fun s => typeof C (y/V s)))); reflexivity.
      * reflexivity.
    + intros. unfold liftn, lift, var_expr, typeof, open_eq, val_class in *; simpl in *.
      destruct H as [p [H1 H2]]; rewrite H1; simpl; intuition.
  Qed.

  Lemma xist_from_post U P c (Q : U -> sasn) :
    (Exists x:U, {[ P ]} c {[ Q x ]}) |-- {[ P ]} c {[ Exists x, Q x ]}.
  Proof.
  	apply lexistsL; intro x. eapply roc_post; [|apply lexistsR with x]; reflexivity.
  Qed.

Ltac existentialise y v :=
	rewrite existentialise_triple with (x := y); intro v; [reflexivity|].

  Lemma rule_call_old C m ps (es : list dexpr) (x y r : var) (P Q : sasn)
    (HLen : length ps = length ((E_var y) :: es)) :
    |> (C :.: m |-> ps {{ P }}-{{ r, Q}}) |--
      {[@lembedand vlogic sasn _ _ (`typeof `C y/V) (P //! zip ps ((y/V) :: (map (fun e s => eval e s) es)))]}
      cdcall x y m es
      {[Exists v:val, Q //! zip (r :: ps)
          ( (x/V) :: (y/V)[{`v // x}] ::
            map (fun e => e[{`v//x}]) (map (fun e s => eval e s) es))]}.      
  Proof.
    intros. existentialise x v. 
    rewrite rule_call_dynamic; [|eapply HLen].
    rewrite <- xist_from_post. apply lforallL with v. apply lexistsR with v.
    unfold lembedand. rewrite <- embedland, landA. reflexivity.
  Qed.

  Lemma rule_assign x (e : dexpr) (P : sasn) (G : spec) :
    G |-- {[P [{(eval e) // x}]]} cassign x e {[P]}.
  Proof.
  	unfold triple; apply lforallR; intro sc; apply lpropimplR; intro Hsem.
  	inversion Hsem; subst. simpl; split; intros.
  	+ intro HFail. inversion HFail.
  	+ inversion H4; subst.
  	  unfold apply_subst in H3. solve_model H3.
  	  rewrite subst1_stack. reflexivity.
  Qed.

  Lemma rule_assign_fwd G P Q x (e : dexpr) 
    (H : Exists v:val, @lembedand vlogic sasn _ _ (open_eq (x /V) ((eval e) [{`v // x}])) (P [{`v // x}]) |-- Q) :
    G |-- {[ P ]} cassign x e {[ Q ]}.
  Proof.
  	eapply roc_pre; [|eapply rule_assign].
  	intros s Pr n h HP.
  	specialize (H (stack_add x (eval e s) s) Pr n h).
  	simpl in *. assert ((((Q (stack_add x (eval e s) s)) Pr) n) h).
  	+ apply H. exists (s x). split.
  	  * unfold open_eq, var_expr. rewrite stack_lookup_add. 
  	    unfold apply_subst. rewrite subst1_stack, stack_add_overwrite.
  	    unfold liftn, lift; simpl. rewrite stack_add_same. reflexivity.
  	  * unfold apply_subst. solve_model HP.
  	    rewrite subst1_stack, stack_add_overwrite.
  	    unfold liftn, lift; simpl. rewrite stack_add_same. reflexivity.
  	+ unfold apply_subst. solve_model H0. rewrite subst1_stack. reflexivity.
  Qed.

  Lemma rule_dcall_forward C m ps (es : list dexpr) (x y r : var) G
  (P Q F Pm Qm : sasn) 
    (Hspec : G |-- |> C :.: m |-> ps {{ Pm }}-{{ r, Qm }})
    (HPre : P |-- (@lembedand vlogic sasn _ _ (`typeof (`C) (y/V)) (Pm //! zip ps (map (fun e s => eval e s) ((E_var y)::es)))
      ** F))
    (HLen : length ps = length (E_var y :: es))
    (HPost : Exists v:val, @lembedand vlogic sasn _ _ ((`typeof (`C) (y/V))[{`v//x}])
     (Qm //! (zip (r :: ps) ((x/V) :: (y/V)[{`v//x}] ::
        map (fun e => e[{`v//x}]) (map (fun e s => eval e s) es))) ** F[{`v//x}]) |-- Q) :
    G |-- {[ P ]} cdcall x y m es {[ Q ]}.
  Proof.
  	existentialise x v.
  	rewrite HPre.
  	eapply roc_pre with (P' := 
  	    (@lembedand vlogic sasn _ _ (@land vlogic _ (open_eq x/V (fun _ => v)) (fun s => typeof C (y/V s)))
         (Pm //! zip ps (map (fun (e : dexpr) (s : Stack.stack) => eval e s) ((E_var y) :: es)))) **
        (@lembedand vlogic sasn _ _ (open_eq x/V (fun _ => v)) 
        (@lembedand vlogic sasn _ _ (fun s => typeof C (y/V s)) F))).
     clear Hspec HPre HLen HPost.
     intros s Pr n h [H1 [h1 [h2 [Hh [[H3 H4] H5]]]]].
     simpl in *. exists h1, h2, Hh; (repeat split); assumption.
     eapply roc_post; [eapply rule_frame|].
     revert v. apply lforallR2.
     rewrite Hspec. apply rule_call_dynamic.
     assumption. rewrite <- HPost. apply lexistsR with v.
     unfold subst_mod_asn. rewrite bilexistsscR. apply lexistsL; intro vs.
     simpl.      unfold SS.MSet.Raw.singleton, apply_subst, subst_fresh,
                   open_eq, liftn, lift, var_expr, substl_trunc, subst1; simpl.
     clear HPre HLen HPost Hspec.
     intros s pr n h [h1 [h2 [Hh [H1 [H2 [H3 H4]]]]]].
     unfold stack_subst in *; simpl in *.
     destruct (string_dec x x); [|congruence].
     destruct (string_dec x y).
     destruct (@string_dec y x); [|congruence].
     split; [intuition congruence|].
     exists h1, h2, Hh. split.
     solve_model H1. solve_model H4.
     apply functional_extensionality. intros; simpl.
     destruct (string_dec x0 x).
     destruct (string_dec x x0); congruence.
     destruct (string_dec x x0); [congruence | reflexivity].
     destruct (string_dec y x); [congruence|].
     split. apply H3.
     exists h1, h2, Hh. split.
     solve_model H1. solve_model H4.
     apply functional_extensionality. intros.
     destruct (string_dec x x0);
     destruct (string_dec x0 x); unfold var_expr; simpl;
     intuition congruence.
  Qed.

  Lemma rule_static_complete C m ps (es : list dexpr) (x r : var) G
    (P Q F Pm Qm : sasn)
    (HSpec : G |-- |> C :.: m |-> ps {{ Pm }}-{{ r, Qm }})
    (HPre: P |-- (Pm //! zip ps (map (fun e s => eval e s) es)) ** F)
    (HLen: length ps = length es)
    (HPost : Exists v:val, Qm //! zip (r :: ps) ((x/V) ::
                                      map (fun e => e[{`v//x}]) 
                                          (map (fun e s => eval e s) es)) ** 
                           F[{`v//x}] |-- Q) :
          G |-- {[ P ]} cscall x C m es {[ Q ]}.
  Proof.
  	existentialise x v.
  	rewrite HPre.
  	eapply roc_pre with (P' := 
  	    (@lembedand vlogic sasn _ _ (open_eq x/V (fun _ => v))
         (Pm //! zip ps (map (fun (e : dexpr) (s : Stack.stack) => eval e s) es))) **
        (@lembedand vlogic sasn _ _ (open_eq x/V (fun _ => v)) F)).
     clear HSpec HPre HLen HPost.
     intros s Pr n h [H1 [h1 [h2 [Hh [H3 H4]]]]].
     simpl in *. exists h1, h2, Hh; (repeat split); assumption.
     eapply roc_post; [eapply rule_frame|].
     revert v. apply lforallR2.
     rewrite HSpec. apply rule_call_static.
     assumption. rewrite <- HPost. apply lexistsR with v.
     unfold subst_mod_asn. rewrite bilexistsscR. apply lexistsL; intro vs.
     simpl.      unfold SS.MSet.Raw.singleton, apply_subst, subst_fresh,
                   open_eq, liftn, lift, var_expr, substl_trunc, subst1; simpl.
     clear HPre HLen HPost HSpec.
     intros s pr n h [h1 [h2 [Hh [H1 [H2 H3]]]]].
     unfold stack_subst in *; simpl in *.
     destruct (string_dec x x); [|congruence].
     exists h1, h2, Hh. split.
     solve_model H1. solve_model H3.
     apply functional_extensionality. intros.
     destruct (string_dec x x0);
     destruct (string_dec x0 x); unfold var_expr; simpl;
     intuition congruence.
  Qed.

(* TODO: move to Pwf *)
Lemma ext_fields_same PP PP' C fields
  (HPP : Prog_wf_sub PP PP')
  (HF  : field_lookup PP C fields) :
  exists fields', SS.Equal fields fields' /\ field_lookup PP' C fields'.
Proof.
  destruct HF as [crec [HF HT]]; rewrite SM'.find_mapsto_iff in HF.
  specialize (HPP _ _ HF); destruct HPP as [crec' [HF' [HT' _]]].
  subst; eexists; split; [eassumption | eexists; split; rewrite ?SM'.find_mapsto_iff; eassumption || reflexivity].
Qed.
Lemma equiv_alloc_same fields fields' P p
  (HEq : SS.Equal fields fields') :
  (SS.fold (fun f Q => `pointsto `(vptr p) `f `null ** Q) fields P -|- SS.fold (fun f Q => `pointsto `(vptr p) `f `null ** Q) fields' P).
Proof.
  apply SS'.fold_equal; [apply _ | | | assumption].
  + intros f f' EQf Q Q' HQ; subst f'. rewrite HQ; reflexivity.
  + intros f f' Q. repeat rewrite <- sepSPA. 
    split; apply bilsep; rewrite sepSPC; reflexivity.
Qed.

(*
  Lemma rule_alloc_ax (x : var) C fields :
    [prog](fun Pr => field_lookup Pr C fields) |-- {[ ltrue ]} calloc x C {[ Exists p:ptr,
      @lembedand pure sasn _ _ (@land pure _ (`typeof `C (x/V)) (open_eq x /V `(vptr p)))
      (SS.fold (fun f Q => `pointsto `(vptr p) `f `null ** Q) fields ltrue)]}.
  Proof.
  	unfold triple. lforallR sc. apply lpropimplR; intro HSem.
  	inversion HSem; subst; clear HSem.
  	intros Pr n HLookup Pr' m k s h HPr Hm Hk _; split; [intro H; inversion H|].
  	intros h' s' HSem; inversion HSem. subst; clear HSem. exists (n0, C).
    split. unfold var_expr, liftn, lift, open_eq, typeof; simpl. rewrite stack_lookup_add.
    	split; [exists (n0, C); intuition congruence |reflexivity]. 
    specialize (HLookup _ HPr); simpl in HLookup.
    assert (fields0 = fields) by (eapply field_lookup_function; eauto); subst.
    clear Sfields. 
    generalize dependent h1. generalize dependent h'0.
    apply (@SS'.set_induction) with (s := fields); intros.
    rewrite SS'.fold_1b; [simpl; intuition |assumption].
    assert (SS.fold (fun (f : SS.elt) (Q : sasn) => 
                     `pointsto `(vptr(n0, C)) `f `null ** Q) s' ltrue -|-
           `pointsto `(vptr(n0, C)) `x0 `null **
            (SS.fold (fun (f : SS.elt) (Q : sasn) => 
                     `pointsto `(vptr(n0, C)) `f `null ** Q) s0 ltrue)). {
    rewrite SS'.fold_2; [reflexivity | apply _| | | assumption | assumption].
    + unfold compat_op. intros a b c d e f. subst. rewrite f. reflexivity.
    + unfold transpose. intros. repeat rewrite <- sepSPA. rewrite (sepSPC (`pointsto `(vptr(n0, C)) `x1 `null)).
      reflexivity.
    }
    apply H2; clear H2.
    rewrite (@SS'.fold_2 s0 s' x0 heap_ptr rel) in Sh0; [| apply _ | | | eassumption | assumption].
    + exists ((add (n0, C, x0) null heap_ptr_unit, h'0)). 
      exists (((SS.fold
              (fun (f : SS.elt) (h' : heap_ptr) =>
               add (n0, C, f) null h1) s0 heap_ptr_unit)), h'0). eexists. admit.
      split. unfold liftn, lift, pointsto; simpl.
      split. unfold null. intuition congruence.
      unfold SepAlg.subheap. exists heap_ptr_unit.
      simpl. admit.
      apply (H h'0).
      Require Import SepAlg.
      Transparent sa_mul.
      intros [ptr f]. unfold heap_ptr_unit. simpl. 
      unfold sa_mul in Sh0. simpl in Sh0.
      specialize (Sh0 (ptr, f)). simpl in *.
      rewrite empty_in_iff.
      SearchAbout MapInterface.In empty. rewrite empty_in_iff in H3. destruct H3.
      admit.
    + unfold compat_op; intros a b Hab c d Hcd; subst. rewrite Hcd. reflexivity.
    + unfold transpose. intros a b Hmap. intros d.
      destruct (eq_dec (n0, C, a) d);
      destruct (eq_dec (n0, C, b) d).
      do 2 (rewrite add_eq_o; [|assumption]); reflexivity.
      rewrite add_eq_o; [|assumption]; rewrite add_neq_o; [|assumption].
      rewrite add_eq_o; [|assumption]. reflexivity.
      rewrite add_neq_o; [|assumption]; rewrite add_eq_o; [|assumption].
      rewrite add_eq_o; [|assumption]. reflexivity.
      do 4 (rewrite add_neq_o; [|assumption]). reflexivity.
Qed.

  Lemma rule_alloc : forall (x : var) C fields (PP : Prog_wf),
    field_lookup PP C fields ->
    (|= {[ <true> ]} calloc x C {[
      SS.fold (fun f Q => x /V · `f >> `null <*> Q) fields
        <true> </\> <pure> x ::: C ]} @ PP)%spec%asn.
  Proof.
    introv HLU.
    eapply roc_post; [apply rule_alloc_ax; eassumption |].
    unfold_stack s; ent_nf.
    rewrite <- H0.
    apply SS'.fold_rel with (f:= \f, \Q, `(s x) · `f >> `null <*>Q)
      (g := \f, \Q, x/V · `f >> `null <*> Q); [sl_simpl |].
    intros; rewrite !true_and_eq_unitR in *.
    simpl; rewrite H2; reflexivity.
  Qed.

  Lemma rule_alloc_fwd : forall (x : var) C fields P G (PP : Prog_wf),
    field_lookup PP C fields ->
    (G |= {[ P ]} calloc x C
          {[ (<pure> x ::: C </\>
              SS.fold (fun f Q => (x:expr) · `f >> `null <*> Q) fields <true>) <*>
              <E>v:val, P[{`v//x}] ]} @ PP)%spec%asn.
  Proof.
    introv HLU.
    rewrite true_specR.
    eapply roc_pre; [sl_apply true_sc_unitL |].
    eapply roc_post; [| sl_apply sc_upME; [reflexivity|]].
    > apply rule_frame. sl_rewriter and_upC. 
      apply rule_alloc. eassumption.
    unfold subst_mod_asn; simpl; unfold SS.MSet.Raw.singleton.
    sl_existE vs.
    rewrite subst_fresh1.
    sl_exists (vs x); reflexivity.
  Qed.
  Implicit Arguments rule_alloc_fwd [[x] [C] [fields] [P] [G]].
*)
