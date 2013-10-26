Require Import Morphisms Setoid Rel.
Require Import ILogic ILEmbedTac ILQuantTac ILInsts ILEmbed Later SepAlgMap.
Require Import SpecLogic Pure AssertionLogic Program Open Stack Subst.
Require Import OperationalSemantics Lang.
Require Import MapInterface MapFacts SemCmd SemCmdRules.

Set Implicit Arguments.
Unset Strict Implicit.

  Add Parametric Morphism : triple with signature
    lentails --> lentails ++> eq ==> lentails
    as c_triple_entails_m.
  Proof.
    intros p p' Hp q q' Hq c.
    unfold triple. 
    setoid_rewrite Hq; setoid_rewrite <- Hp. reflexivity.
  Qed.


Local Transparent ILFun_Ops.
Local Transparent ILLaterPreOps.

  (* TODO: move that somewhere earlier, say, AbstractAsn *)
  Add Parametric Morphism : apply_subst with signature
      lentails ++> eq ==> lentails
        as open_subst_entails_asn_m.
  Proof.
  	intros x y Hxy sub1 sub2. apply Hxy.
  Qed.

  Add Parametric Morphism : method_spec with signature
    eq ==> eq ==> eq ==> eq ==>
      lentails --> lentails ++> lentails
    as method_spec_entails_m.
  Proof.
    intros C m ps rn P P' HP Q Q' HQ. unfold method_spec.
    (* Unravel the two almost identical sides of the entailment first because
        setoid_rewrite doesn't seem to go under these binders. *)
    lpropandL H. lpropandR; [assumption|].
    lexistsL ps' c re. lexistsR ps' c re.
    apply landR; [apply landL1; reflexivity | apply landL2].
    setoid_rewrite HP. setoid_rewrite HQ. reflexivity.
  Qed.

  Local Transparent ILPre_Ops.

  Lemma triple_false (G : spec) (Q : sasn) c :
    G |-- {[lfalse]} c {[Q]}.
  Proof.
    intros n; simpl in *; intros; destruct H4.
  Qed.

  Add Parametric Morphism : method_spec with signature
    eq ==> eq ==> eq ==> eq ==>
      lequiv ==> lequiv ==> lequiv
    as method_spec_bientails_m.
  Proof.
    split; apply method_spec_entails_m; try rewrite ?H, ?H0; reflexivity.
  Qed.


Opaque ILPre_Ops.


  Lemma roc (P P' Q Q' : sasn) c (G : spec)
    (HPre  : P  |-- P')
    (HPost : Q' |-- Q)
    (Hc    : G  |-- {[P']} c {[Q']}) :
    G |-- {[P]} c {[Q]}.
  Proof.  
  	rewrite Hc.
  	unfold triple. lforallR sc. apply lpropimplR; intros Hsc.
  	lforallL sc. apply lpropimplL; [assumption|]. apply rule_of_consequence; assumption.
  Qed.

  Lemma roc_pre (P P' Q : sasn) c G
    (HPre : P |-- P')
    (Hc   : G |-- {[P']} c {[Q]}) :
    G |-- {[P]} c {[Q]}.
  Proof.
  	eapply roc; eassumption || reflexivity.
  Qed.

  Lemma roc_post (P Q Q' : sasn) c G
    (Hc : G  |-- {[P]} c {[Q']})
    (HPost : Q' |-- Q) :
    G |-- {[P]} c {[Q]}.
  Proof.
    eapply roc; eassumption || reflexivity.
  Qed.

Transparent ILPre_Ops.
Local Transparent EmbedAsnPureOp.
Local Transparent EmbedILFunOp.
Local Transparent EmbedAsnPropOp.
Local Transparent EmbedILPreDropOpEq.
Local Transparent ILPre_Ops.
Local Transparent EmbedILPreDropOpEq.
Local Transparent EmbedILPreOp.
Local Transparent EmbedILPreDropOpNeq.
Local Transparent MapSepAlgOps.
Local Transparent ILFun_Ops.
Local Transparent EmbedILFunDropOp.
Local Transparent EmbedILFunOp.

  Lemma rule_read_fwd (x y : var) (f : field) (e : expr) (P : sasn)
    (HPT : P |-- `pointsto y/V `f e) :
   @ltrue spec _ |-- {[ P ]} cread x y f {[ Exists v : val, @lembedand pure sasn _ _ (open_eq (x /V) (e [{`v//x}])) (P[{`v//x}])]}.
  Proof.
    unfold triple in *; intros. lforallR sc. apply lpropimplR; intros Hsem.
    inversion Hsem; subst.
    unfold sem_triple; simpl; split; intros.
    + intro HFail; inversion HFail; subst. apply Snotin; clear Snotin HFail.
      specialize (HPT _ _ _ _ H3); unfold pointsto in HPT;
        simpl in HPT; destruct HPT as [Hnull [h' HPT]].
        specialize (HPT (ref, f)). unfold var_expr in HPT. rewrite Sref in HPT.
        unfold liftn, lift in HPT; simpl in HPT.
        remember (@find (ptr * field) _ _ sval (ref, f) h) as o.
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
        specialize (HPT (ref, f)). remember (find (ref, f) h') as o.
	    destruct o; [destruct HPT as [[HPT HIn] | [Hm HPT]] | destruct HPT as [HPT _]].
        - rewrite add_mapsto_iff in HPT. destruct HPT as [[Heq HPT] | [Hneq HPT]]. 
          rewrite Rref0 in Heq. simpl in Heq.
          rewrite <- HPT in Heqo. rewrite find_mapsto_iff in Rmaps.
          rewrite Rmaps in Heqo. inversion Heqo. reflexivity.
          assert False as HFalse. apply Hneq. rewrite Rref. reflexivity.
          destruct HFalse.
        - rewrite add_in_iff in HPT. assert False as HFalse
          	by (apply HPT; left; rewrite Rref; reflexivity); destruct HFalse.
        - rewrite add_in_iff in HPT. assert False as HFalse
          	by (apply HPT; left; rewrite Rref; reflexivity); destruct HFalse.
      * solve_model H3.
  Qed.

Require Import String List.

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
      simpl. destruct (dec_eq x' yh).
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
	  simpl. destruct (dec_eq x p).
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
    stack_subst (zip ps' es :@: s +:+ stack_empty var)
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
      simpl. destruct (dec_eq x p).
      * unfold var_expr. simpl. autorewrite with stack. reflexivity.
      * etransitivity; [|apply IHps with (ps':=ps')].
        - apply substl_trunc_add.
          inversion HND0. assumption.
          inversion HLen. reflexivity.
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
      simpl. destruct (dec_eq x' a).
      * simpl. symmetry. apply H. auto with datatypes.
      * apply IHps. auto with datatypes.
  Qed.
 
  Lemma rule_call_sem (C : class) (m : method) (ps : list var) (r x : var) (P Q : sasn) (es : list dexpr) c sc
    (CC : @open var _ class) (T : sasn)
    (HSem : semantics c sc)
    (HEnt :  forall PP s h n, (T s PP h n) -> (open_eq CC `C) s)
    (HLen : length ps = length es) :
    |> (C :.: m |-> ps {{ P }}-{{ r, Q}}) |-- @lforall spec _ _ (fun v : val => 
      {{@lembedand pure sasn _ _ (open_eq (x/V) (`v)) (P //! zip ps (map (fun e s => eval e s) es) //\\ T)}}
      (call_cmd x (liftn C) m es c sc)
      {{Q //! zip (r :: ps) (((x/V):expr) :: map (fun e => e[{`v // x}]) (map (fun e s => eval e s) es))}}).
  Proof.
  	lforallR v.
  	intros p n H p2 m' k s h Hsub Hm'n Hkm' [Hh HP].
  	destruct n; simpl in *.
  	
  	(* No fuel *) {
   	assert (k = 0) by omega; subst. split.
   	+ apply call_cmd_obligation_1.
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
	    destruct HP. unfold apply_subst in *.
	    solve_model H.
        erewrite <- substl_trunc_subst; [reflexivity|..]. 
        apply prog_wf in HML. apply HML.
        assumption. assumption. 
      * assert (HT := method_lookup_function HML HLookup); injection HT; intros;
        subst; congruence.
    +  
    (* correctness *)
    intros h' s' HSem1; inversion HSem1; subst; clear HSem1.
    assert (HPS := method_lookup_function HLookup HML);
      inversion HPS; subst; clear HPS HLookup.
    edestruct HOK with (x := sc) (x2:=m'-1) (k:=n0) (h:=h) 
    (s := (create_stack args (eval_exprs s es))) as [_ HC];
    	clear HOK; [eassumption | omega | assumption | reflexivity | reflexivity | omega | ..].
    destruct HP. unfold apply_subst in *.
    solve_model H.
    unfold apply_subst. erewrite substl_trunc_subst.
    reflexivity.
    apply prog_wf in HML. apply HML. omega. omega. 
    unfold apply_subst in *.
    specialize (HC _ _ HSem0).
    solve_model HC.
    (* equality of post stack *)
    apply functional_extensionality. intros z. unfold stack_subst. simpl. destruct (dec_eq z r).
    * case (dec_eq z r); [intros |congruence]. 
      unfold var_expr. rewrite stack_lookup_add. reflexivity.
    * case (dec_eq z r); [congruence|intros].
      
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
        * subst p. do 2 (case (dec_eq z z); [intro|congruence]). 
          unfold var_expr. simpl. autorewrite with stack. simpl.
          unfold subst1, liftn, var_expr. simpl.
          unfold eval. f_equal.
          apply functional_extensionality. intros. simpl.
          case (dec_eq x0 x). intros. simpl.
          unfold lift. subst. admit. intros.
          rewrite stack_lookup_add2. reflexivity. intuition.
        * do 2 (case (dec_eq z p); [congruence|intro]). 
          rewrite substl_trunc_add. apply IHps. simpl in *. omega. simpl in *.
          inversion HML. assumption. simpl in *. omega. inversion HML. assumption.
          simpl in *. omega.
      }
    - intros p' HIn. pose modifies_syn_sem as Hmod.
      unfold c_not_modifies, not_modifies in Hmod. eapply Hmod; [| eassumption|].
      auto. apply HSem0.
 Qed.

  Lemma rule_call_static : forall PP C m ps (es : list expr) (x r : var) P Q
    (HLen : length ps = length es),
    (|> (C :.: m |-> ps {{ P }}-{{ r, Q }}) |= [A] v:val,
      {[ x /V == `v </\> P //! zip ps es ]} cscall x C m es
      {[Q //! zip (r :: ps) ((x:expr) :: map (\e, e[{`v//x}]) es)]} @ PP)
    %asn%spec.
  Proof.
    intros; unfold c_triple; spec_all v; spec_all sc.
    apply pure_impl_specR; intros HSem; inversion HSem; subst.
    (sl_rewritel and_upI); [reflexivity | sl_apply true_upR|].
    sl_rewritel and_upA.
    revert v; apply -> all_specEIR.
    apply rule_call_sem; [assumption | reflexivity| assumption].
  Qed.

  Lemma rule_call_dynamic : forall PP C m ps (es : list expr) (x y r : var) P Q
    (HLen : length ps = length ((y:expr) :: es)),
    (|> (C :.: m |-> ps {{ P }}-{{ r, Q}}) |= [A] v:val,
      {[ x /V == `v </\> <pure> y ::: C </\> P //! zip ps ((y:expr) :: es) ]}
      cdcall x y m es
      {[Q //! zip (r :: ps)
        ((x:expr) :: (y:expr) [{`v // x}] :: map (\e, e[{`v//x}]) es) ]} @ PP)
    %asn%spec.
  Proof.
    intros; unfold c_triple; spec_all v; spec_all sc.
    apply pure_impl_specR; intros HSem; inversion HSem; subst.
    sl_rewritel and_upC with (p := (<pure> y ::: C)).
    revert v; apply -> all_specEIR.
    apply rule_call_sem; [assumption | | assumption].
    intros s; simpl; trivial.
  Qed.

  Lemma xist_from_post PP U P c (Q : U -> hasn) :
    (([E] x:U, {[ P ]} c {[ Q x ]}) |= {[ P ]} c {[ <E> x, Q x ]} @ PP)%spec.
  Proof.
    apply xist_specEIL; intros x n PP' HPP HP; simpl in *; intros.
    specialize (HP _ _ _ H H0 H1 _ _ _ _ _ H2 H3 H4 H5); intuition eauto.
  Qed.

(*Implicit Arguments existentialize [V S].*)

  Lemma rule_call_old : forall C m ps (es : list expr) (x y r : var) (P Q : hasn)
    (HLen : length ps = length ((y:expr) :: es)) PP,
    (|> (C :.: m |-> ps {{ P }}-{{ r, Q}}) |=
      c_triple (<pure> y ::: C </\> P //! zip ps ((y:expr) :: es))
        (<E> v:val, Q //! zip (r :: ps)
          ( (x:expr) :: (y:expr)[{`v // x}] ::
            map (\e, e[{`v//x}]) es))
        (cdcall x y m es) @ PP)%asn%spec.
  Proof.
    intros.
    sl_rewritel existentialize with (x := (vvar_expr x)).
    rewrite <- exists_into_precond_c; spec_all v.
    rewrite <- xist_from_post; apply xist_specIR; exists v.
    revert v; apply -> all_specEIR; apply rule_call_dynamic; assumption.
  Qed.

  (* TODO: needed? *)
  Lemma rule_frame_ax_list : forall P Q R c (xs: list var) PP
    (HMod : forall x, ~ In x xs -> c_not_modifies c x), (
    {[ P ]} c {[ Q ]} |=
    {[ P <*> R ]} c {[ Q <*> <E>vs, open_subst R (subst_fresh vs xs) ]} @ PP
  )%spec%asn.
  Proof.
    unfold c_triple in *; intros.
    apply all_specEIR. intro sc. apply all_specEL with sc.
    apply pure_impl_specR. intro Hsem. apply pure_impl_specL; [assumption|].
    apply frame_rule. unfold c_not_modifies in HMod. auto.
  Qed.

  Definition subst_mod_asn (R: hasn) (c: cmd) : hasn :=
    <E>vs, open_subst R (subst_fresh vs (SS.elements (modifies c))).

  Lemma rule_frame_ax P Q R c PP : (
    {[ P ]} c {[ Q ]} |=
    {[ P <*> R ]} c {[ Q <*> subst_mod_asn R c ]} @ PP
  )%spec%asn.
  Proof.
    apply rule_frame_ax_list. intros x HnotIn. apply modifies_syn_sem.
    rewrite SS'.In_elements_iff. assumption.
  Qed.

  (* TODO: needed? *)
  Lemma rule_frame_list P Q R c G (xs: list var) PP
    (HMod : forall x, ~ In x xs -> c_not_modifies c x)
    (HPre : (G |= c_triple P Q c @ PP)%spec) : (
    (G |= c_triple (P <*> R) (Q <*> <E>vs, open_subst R (subst_fresh vs xs)) c @ PP)
  )%asn%spec.
  Proof.
    intros; rewrite <- rule_frame_ax_list; assumption.
  Qed.

  Lemma rule_frame P Q R c G PP
    (HPre : (G |= {[P]} c {[Q]} @ PP)%spec) : (
    G |= {[ P <*> R ]} c {[ Q <*> subst_mod_asn R c ]} @ PP
  )%asn%spec.
  Proof.
    intros; rewrite <- rule_frame_ax; assumption.
  Qed.
  Implicit Arguments rule_frame [[P] [Q] [R] [c] [G]].

  Lemma rule_seq_ax : forall c1 c2 (P Q R : hasn) PP,
    ((c_triple P Q c1 [/\] c_triple Q R c2) |= c_triple P R (cseq c1 c2) @ PP)%spec.
  Proof.
    unfold c_triple in *; intros.
    apply all_specEIR. intro sc.
    apply pure_impl_specR. intro Hsem. inversion Hsem. subst.
    rewrite distr_all_and_specL. eapply all_specEL. rewrite and_specC.
    rewrite distr_all_and_specL. eapply all_specEL.
    rewrite distr_impl_and_L. apply pure_impl_specL; [eassumption|].
    rewrite and_specC.
    rewrite distr_impl_and_L. apply pure_impl_specL; [eassumption|].
    apply seq_rule.
  Qed.

  Lemma rule_seq : forall c1 c2 (P Q R : hasn) G PP
    (Hc1 : (G |= c_triple P Q c1 @ PP)%spec)
    (Hc2 : (G |= c_triple Q R c2 @ PP)%spec),
    (G |= c_triple P R (cseq c1 c2) @ PP)%spec.
  Proof.
    intros; rewrite <- rule_seq_ax; apply and_specI; eassumption.
  Qed.

  Lemma rule_if_ax : forall (e : expr) c1 c2 (P Q : hasn) PP,
    ((c_triple (P </\> <pure> expr_pure e) Q c1 [/\] c_triple (P </\> <pure> expr_pure (enot e)) Q c2)
    |= c_triple P Q (cif e c1 c2) @ PP)%asn%spec.
  Proof.
    unfold c_triple in *; intros.
    apply all_specEIR. intro sc.
    apply pure_impl_specR. intro Hsem. inversion Hsem. subst.
    rewrite distr_all_and_specL. eapply all_specEL. rewrite and_specC.
    rewrite distr_all_and_specL. eapply all_specEL.
    rewrite distr_impl_and_L. apply pure_impl_specL; [eassumption|].
    rewrite and_specC.
    rewrite distr_impl_and_L. apply pure_impl_specL; [eassumption|].
    rewrite and_specC.
    rewrite <- nondet_rule; apply and_specI; rewrite <- seq_rule;
      [apply and_specER | apply and_specEL]; (apply and_specI;
        [rewrite true_specR | reflexivity]; apply assume_rule).
  Qed.

  Lemma rule_if : forall (e : expr) c1 c2 (P Q : hasn) G PP
    (Hc1 : (G |= c_triple (P </\> <pure> (expr_pure e))%asn Q c1 @ PP)%spec)
    (Hc2 : (G |= c_triple (P </\> <pure> (expr_pure (enot e)))%asn Q c2 @ PP)%spec),
    (G |= c_triple P Q (cif e c1 c2) @ PP)%spec.
  Proof.
    intros; rewrite <- rule_if_ax; apply and_specI; assumption.
  Qed.

  Lemma rule_while_ax : forall (e : expr) c (P : hasn) PP,
    ((c_triple (P </\> <pure> (expr_pure e)) P c) |=
      c_triple P (P </\> <pure> (expr_pure (enot e))) (cwhile e c) @ PP)%asn%spec.
  Proof.
    unfold c_triple in *; intros.
    apply all_specEIR. intro sc.
    apply pure_impl_specR. intro Hsem. inversion Hsem. subst.
    eapply all_specEL. apply pure_impl_specL; [eassumption|].
    rewrite <- seq_rule; apply and_specI;
      [| rewrite true_specR; apply assume_rule].
    rewrite <- kleene_rule, <- seq_rule; apply and_specI; [| reflexivity].
    rewrite true_specR; apply assume_rule.
  Qed.

  Lemma rule_while : forall (e : expr) c (P : hasn) G PP
    (Hc : (G |= {[P </\> <pure> (expr_pure e)]} c {[P]} @ PP)%spec),
    (G |= {[P]} cwhile e c {[P </\> <pure> (expr_pure (enot e))]} @ PP)%spec.
  Proof.
    intros; rewrite <- rule_while_ax; assumption.
  Qed.

  Lemma rule_assert : forall (e : expr) P G PP
    (HPe : (P |- <pure> (expr_pure e))%asn),
    (G |= {[ P ]} cassert e {[ P ]} @ PP)%spec.
  Proof.
    unfold c_triple; intros; spec_all sc.
    apply pure_impl_specR; intro HSem; inversion HSem; subst.
    rewrite true_specR; apply assert_rule.
    rewrite HPe; intros s; simpl.
    destruct (e s); simpl; intros h n; simpl; congruence.
  Qed.

  Lemma rule_skip_ax P PP :
    (|= {[P]} cskip {[P]} @ PP)%spec.
  Proof.
    unfold c_triple. apply all_specEIR. intro sc.
    apply pure_impl_specR. intro Hsem.
    inversion Hsem. subst. apply skip_rule.
  Qed.

  Lemma rule_skip P G PP :
    (G |= {[P]} cskip {[P]} @ PP)%spec.
  Proof.
    etransitivity.
    > apply true_specR.
    > apply rule_skip_ax.
  Qed.

  Lemma rule_skip_fwd P Q G PP
    (HPQ: P |- Q)
  : (G |= {[P]} cskip {[Q]} @ PP)%spec.
  Proof.
    eapply roc_post; [|eassumption].
    etransitivity.
    > apply true_specR.
    > apply rule_skip_ax.
  Qed.

  Lemma rule_assign : forall x e (Q : hasn) (G : spec) PP,
    (G |= c_triple (Q [{e // x}]) Q (cassign x e) @ PP)%spec.
  Proof.
    unfold c_triple in *; intros. apply all_specEIR. intro sc.
    apply pure_impl_specR. intro Hsem. inversion Hsem. subst.
    unfold entails_spec, triple; simpl; split; intros.
    intro HFail; inversion HFail. autorewrite with stack in H4.
    inversion H5; subst; apply up_mono with P'0 h' m; [reflexivity | reflexivity | omega | assumption].
  Qed.

  Lemma rule_assign_fwd G P Q x e PP :
    (<E>v:val, P [{`v // x}] </\> x /V == (e [{`v // x}]) |- Q)%asn ->
    (G |= {[ P ]} cassign x e {[ Q ]} @ PP)%spec.
  Proof.
    intros HEnt; rewrite true_specR.
    eapply roc_pre; [| eapply rule_assign].
    unfold entails_asn, open_rel in HEnt.
    simpl in HEnt.
    setoid_rewrite xist_upEIL in HEnt.
    intro s.
    specialize (HEnt (stack_add x (e s) s) (s x)); simpl in *.
    autorewrite with stack. rewrite <- HEnt; clear HEnt.
    apply and_upI.
    > autorewrite with stack. simpl. autorewrite with stack. reflexivity.
    rewrite true_upR.
    intros PP' h n _. simpl. autorewrite with stack.
    simpl. autorewrite with stack. reflexivity.
  Qed.

  Lemma rule_read_fwd : forall (x y : var) f e (P : hasn) PP
    (HPT : (P |- (vvar_expr y) · `f >> e)%asn),
    (|= {[ P ]} cread x y f
      {[ <E> v:val, x /V == e [{`v//x}] </\> P[{`v//x}]]} @ PP)%asn%spec.
  Proof.
    unfold c_triple in *; intros. apply all_specEIR. intro sc.
    apply pure_impl_specR. intro Hsem. inversion Hsem. subst.
    unfold entails_spec, triple; simpl; split; intros.
    > intro HFail; inversion HFail; subst; apply Snotin; clear Snotin HFail.
      specialize (HPT _ _ _ _ H4); unfold pointsto_up in HPT;
        simpl in HPT; destruct HPT as [[h' HPT] HNN].
      rewrite sa_mulC in HPT; eapply heap_In_dot; eauto.
      unfold PSM'.singleton; rewrite PSM'.add_in_iff; auto.
    inversion H5; subst; clear H5.
    specialize (HPT _ _ _ _ H4); simpl in HPT; destruct HPT as [[ht HPT] HNN].
    exists (s x); split.
    > autorewrite with stack. simpl.  autorewrite with stack.
    > unfold sa_mul in HPT; simpl in HPT; unfold dot, PSM'.singleton in HPT; simpl in HPT.
      rewrite PSM'.fold_add with (eqA := lift_option_rel _) in HPT; simpl in HPT;
        auto using trneq_monAdd with typeclass_instances.
      destruct (PSM.find (elt := sval) (val_to_ptr (s y), f) ht);
        [contradiction|]; simpl in HPT;
          rewrite <- HPT, PSM'.find_mapsto_iff, PSM'.add_eq_o in Rmaps;
            [ injection Rmaps; auto | reflexivity ].
      rewrite PSM'.empty_in_iff; intros HC; contradiction.
    autorewrite with stack. simpl. autorewrite with stack.
    erewrite open_prop;
      [eapply up_mono; [reflexivity | reflexivity | | eassumption]; omega |]; eauto.
  Qed.

  Lemma rule_read_fwd2 : forall (x y : var) f e (P Q : hasn) G PP
    (HPT : P |- (vvar_expr y) · `f >> e)
    (HQT: <E> v:val, P [{`v//x}] </\> x /V == e[{`v//x}] |- Q),
    (G |= {[ P ]} cread x y f {[ Q ]} @ PP)%asn%spec.
  Proof.
    intros. etransitivity; [apply true_specR|].
    eapply roc_post; [apply rule_read_fwd; eassumption |].
    sl_tac (setoid_rewrite and_upC); apply HQT.
  Qed.

  (* No built-in frame rule *)
  Lemma rule_call_fwd : forall C m ps (es : list expr) (x y r : var) G PP
  (P Q Pm Qm : hasn), (
    G |= |> C :.: m |-> ps {{ Pm }}-{{ r, Qm }} @ PP ->
    P |- <pure> y ::: C </\> Pm //! zip ps ((y:expr) :: es) ->
    length ps = length ((y:expr) :: es) ->
    (<E> v:val, Qm //! zip (r :: ps)
          ((x:expr) :: (y:expr)[{`v // x}] ::
            map (\e, e[{`v//x}]) es)) |- Q ->
    G |= c_triple P Q (cdcall x y m es) @ PP
  )%asn%spec.
  Proof.
    introv HLen Hmspec HP HQ. eapply roc; try eassumption; [].
    etransitivity; [eassumption|]. apply rule_call_old; assumption.
  Qed.

  Lemma subst_fresh1 (vs: var -> val) (x: var) :
    subst_fresh vs (x::nil) =X= subst1 (V_expr (vs x)) x.
  Proof.
    rewrite subst_fresh_alt. intro x'. unfold subst1. reflexivity.
  Qed.
  Hint Rewrite subst_fresh1 : open.

  Lemma subst1_twice A v (p: open A) e x :
    open_eq p[{V_expr v//x}][{e//x}] p[{V_expr v//x}].
  Proof.
    intro s. simpl. autorewrite with stack. simpl. reflexivity.
  Qed.
  Hint Rewrite subst1_twice : open.

(* TODO: find a place for these lemmas (AbstractAsn?) *)
Section LemmasSubst.
  Context {V: ValNull} {Σ} `{sa : sep_alg Σ}.

 Lemma var_eq_substL (P : asn) (x : var) exp :
  var_expr x == exp </\> P |- P [{exp // x}].
 Proof.
   intros s. rewrite open_subst_stack. rewrite subst1_stack. simpl.
   apply pure_upEL; intros Heq. rewrite <-Heq. autorewrite with stack.
   reflexivity.
 Qed.

Lemma var_eq_substR (P Q : asn) (x : var) exp :
  (P |- Q [{exp // x}]) -> var_expr x == exp </\> P |- Q.
Proof.
  intros HS s; specialize (HS s); simpl in *; apply pure_upEL; intros HEq.
  rewrite HS. rewrite subst1_stack. simpl.
  erewrite <- HEq. autorewrite with stack. reflexivity.
Qed.

Lemma var_eq_subst (P Q : asn) (x : var) (exp : expr):
  (P [{exp // x}] |- Q [{exp // x}]) -> var_expr x == exp </\> P |- Q.
Proof.
  intro HS.
  sl_rewrite and_upI with (p := (<pure> (x/V ·=· exp)));
    [|reflexivity | reflexivity].
  sl_rewrite and_upA. apply var_eq_substR.
  rewrite var_eq_substL. exact HS.
Qed.
End LemmasSubst.

Ltac existentialize y v :=
  (let t := constr:(@existentialize SVal) in
    sl_rewritel t with (x := y));
  (inst; rewrite <- exists_into_precond_c; spec_all v).

Ltac sl_existE v :=
  let s := fresh "s" in
    intro s; simpl; rewrite xist_upEIL; intro v; sl_restore s.


  Ltac frame_left_aux p :=
    let s := fresh "s" in
      intro s; simpl;
      let p := eval simpl in (p s) in 
        extract_pures(*; up_frame_left p; restore_pures; sl_restore s*).

Ltac frame_left p :=
  match goal with
    | |- (_ |- _)%upred => up_frame_left p
    | |- _ |- _ => frame_left_aux p
    | |- _ |= c_triple _ _ _ @ _ => eapply roc_pre; [frame_left_aux p(*; reflexivity*)|]
  end.


  Lemma rule_call_complete : forall C m ps (es : list expr) (x y r : var) G
  (P Q F Pm Qm : hasn) PP, (
    G |= |> C :.: m |-> ps {{ Pm }}-{{ r, Qm }} @ PP ->
    P |- (<pure> y ::: C </\> Pm //! zip ps ((y:expr) :: es))
      <*> F ->
    length ps = length ((y:expr) :: es) ->
    <E> v:val, (<pure> y ::: C)[{`v//x}] </\>
      Qm //! zip (r :: ps) ((x:expr) :: (y:expr)[{`v//x}] ::
        map (\e, e[{`v//x}]) es) <*> F[{`v//x}] |- Q ->
    G |= {[ P ]} cdcall x y m es {[ Q ]} @ PP
  )%asn%spec.
  Proof.
    introv HC HP HLen HQ; rewrite <- HQ, HP, HC.
    existentialize (vvar_expr x) v.
    rewrite <- xist_from_post; apply xist_specIR; exists v.

    eapply roc_pre with (P' := ( x/V == `v </\> (<pure> y ::: C </\> 
              Pm //! zip ps (((vvar_expr y) :: es)))) <*> 
      (<pure> y ::: C </\> ((x/V == `v </\> F)))).
    unfold_stack s; ent_nf; sl_simpl.

    eapply roc_post. eapply rule_frame.
    revert v. apply all_specEIR. apply rule_call_dynamic; assumption.
    unfold_stack s; ent_nf.
    unfold SS.MSet.Raw.singleton in *.
    rewrite subst_fresh_alt.
    unfold stack_subst, subst_fresh in H, H0.
    simpl in H, H0.
    destruct (string_dec x x); [|congruence].
    simpl in H0. subst. simpl.
    sl_simpl.
    destruct (string_dec x y).
    simpl in H. subst.
    unfold stack_subst, subst1.
    destruct (string_dec y y); [sl_simpl |congruence].
    simpl in H.
    unfold stack_subst, subst1.
    destruct (string_dec y x); [congruence| sl_simpl].
  Qed.

  Lemma rule_static_complete : forall C m ps (es : list expr) (x r : var) G
    (P Q F Pm Qm : hasn) PP, (
      G |= |> C :.: m |-> ps {{ Pm }}-{{ r, Qm }} @ PP->
        P |- (Pm //! zip ps es) <*> F ->
          length ps = length es ->
          <E> v:val, Qm //! zip (r :: ps) ((x:expr) ::
            map (\e, e[{`v//x}]) es) <*> F[{`v//x}] |- Q ->
          G |= {[ P ]} cscall x C m es {[ Q ]} @ PP
    )%asn%spec.
  Proof.
    introv HC HP HLen HQ; rewrite <- HQ, HP, HC; clear HC HP HQ P Q G.
    existentialize (vvar_expr x) v.
    rewrite <- xist_from_post; apply xist_specIR; exists v.
    eapply roc_pre with 
    (P' := (((<pure> (x /V ·=· `v)) </\> 
                Pm //! zip ps es) <*> ((<pure> (x /V ·=· `v)) </\> 
                F))).
    unfold_stack s; ent_nf; rewrite true_and_eq_unitR; sl_simpl.
    eapply roc_post; [eapply rule_frame |].
    > revert v. apply all_specEIR. apply rule_call_static; assumption.
    unfold_stack s; ent_nf; sl_simpl.
    unfold SS.MSet.Raw.singleton.
    unfold stack_subst, subst_fresh in H; simpl in H.
    destruct (string_dec x x); [|congruence]; simpl in H.
    rewrite <- H.
    rewrite subst_fresh1; sl_simpl.
  Qed.

Ltac sl_exists x := 
  let s := fresh "s" in 
    intro s; simpl; apply xist_upIR; exists x; sl_restore s.

(* TODO: move to Pwf *)
Lemma ext_fields_same PP PP' C fields
  (HPP : PP ⊑ PP')
  (HF  : field_lookup PP C fields) :
  exists fields', SS.Equal fields fields' /\ field_lookup PP' C fields'.
Proof.
  destruct HF as [crec [HF HT]]; rewrite SM'.find_mapsto_iff in HF.
  specialize (HPP _ _ HF); destruct HPP as [crec' [HF' [HT' _]]].
  subst; eexists; split; [eassumption | eexists; split; rewrite ?SM'.find_mapsto_iff; eassumption || reflexivity].
Qed.
Lemma equiv_alloc_same fields fields' P p
  (HEq : SS.Equal fields fields') :
  (SS.fold (fun f Q => `(vptr p) · `f >> `null <*> Q) fields P -|- SS.fold (fun f Q => `(vptr p) · `f >> `null <*> Q) fields' P)%asn.
Proof.
  apply SS'.fold_equal; [apply bientails_asn_equiv | | | assumption].
  > intros f f' EQf Q Q' HQ; subst f'; intros s; simpl; rewrite (HQ s); reflexivity.
  intros f f' Q; split; sl_simpl.
Qed.

  Lemma rule_alloc_ax : forall (x : var) C fields (PP : Prog_wf),
    field_lookup PP C fields ->
    (|= {[ <true> ]} calloc x C {[ <E> p:ptr,
      SS.fold (fun f Q => `(vptr p) · `f >> `null <*> Q) fields
        <true> </\> <pure> x ::: C </\> x /V == `(vptr p)]} @ PP)%spec%asn.
  Proof.
    intros ? ? ? ? HLU.
    unfold c_triple; spec_all sc.
    apply pure_impl_specR; intros HSem; inversion HSem; subst; clear HSem.
    intros n PP' HPP _; unfold triple; simpl; introv Hm Hk _; split.
    > intro HS; inversion HS.
    intros h0 s0 HSem; inversion HSem; subst; clear HSem; exists ref.
    rewrite stack_lookup_add; split; [| split; reflexivity].
    edestruct ext_fields_same as [fields' [HEQ HLU']]; [etransitivity; [apply HPP | apply Hm] | eassumption |].
    assert (fields0 = fields') by (eapply field_lookup_function; eauto); subst.
    eapply (equiv_alloc_same _ _ HEQ); clear dependent fields; clear Sfields.
    strengthen (forall f, PSM.In (ref, f) h0 -> In f (SS.elements fields')).
    rewrite SS.fold_1 in *; assert (HDup := SS.elements_3w fields').
    remember (SS.elements fields') as l; clear Heql.
    generalize dependent h0; induction l as [|f fs] using rev_ind; intros.
    > rewrite sa_mulC in Sh0; simpl in *; setoid_rewrite <- Sh0 in Sfresh_h;
      intuition.
    apply NoDupA_swap in HDup; [| auto]; rewrite <- app_nil_end in HDup.
    rewrite fold_left_app in *; simpl fold_left in *.
    remember (fold_left (\a:PSM.t val, \e:SS.elt, PSM.add (ref, e) (null:val) a)
      fs (PSM.empty val)) as hh.
    unfold sa_mul in Sh0; simpl in Sh0; unfold dot in Sh0.
    rewrite <- NIn_monAdd_Some in Sh0.
    rewrite PSM'.fold_commutes with (eqA := lift_option_rel _) in Sh0;
      auto using trneq_monAdd with typeclass_instances.
    replace (PSM.fold monAdd h (Some hh)) with (sa_mul h hh) in Sh0 by reflexivity.
    symmetry in Sh0; apply monAddSome in Sh0; destruct Sh0 as [hr [HEq1 HEq2]].
    inversion_clear HDup; symmetry in HEq1.
    specialize (IHfs H0 _ HEq1).
    simpl; destruct IHfs as [HHeap HIn]; split.
    > exists (PSM'.singleton (ref, f) (null:val)) hr; repeat split.
      assert (sa_mul (PSM'.singleton (ref, f) (null:val)) hr =^= Some h0) as HQ; [| rewrite HQ; eexists; apply sa_unitI].
        unfold PSM'.singleton, sa_mul; simpl; unfold dot; simpl.
        rewrite PSM'.fold_add with (eqA := lift_option_rel _); simpl;
          auto using trneq_monAdd with typeclass_instances; [|].
        > destruct (PSM'.In_dec hr (ref, f)).
          > apply HIn in i; contradiction H; apply In_InA; [|assumption].
            split; [intro; reflexivity | intros ? ? ?; symmetry; assumption
              | intros ? ? ? ? ?; etransitivity; eassumption].
          simpl in *; rewrite PSM'.not_find_in_iff in n0; rewrite n0, HEq2; reflexivity.
        rewrite PSM'.empty_in_iff; tauto.
      > exists sa_unit; apply sa_unitI.
      > assumption.
      assumption.
    intros ff HffIn.
    rewrite <- HEq2 in HffIn.
    rewrite PSM'.add_in_iff in HffIn.
    apply in_or_app; destruct HffIn; [| left; apply HIn; assumption].
    inversion H1; subst; right; intuition.
    > inversion_clear HDup; subst hh; intro HIn.
      apply H; apply In_InA; [auto with typeclass_instances |].
      clear H H0 IHfs Sh0.
      induction fs using rev_ind; simpl in *.
      > rewrite PSM'.empty_in_iff in HIn; assumption.
      rewrite fold_left_app in HIn; simpl in *; rewrite PSM'.add_in_iff in HIn;
        destruct HIn as [HL | HIn]; [inversion HL; subst |]; apply in_or_app.
      > simpl; auto.
      left; apply IHfs; exact HIn.
  Qed.

Ltac sl_unify :=
  let s := fresh "s" in
    intro s; simpl; extract_pures; inst;
    (repeat progress match goal with
      | H : context [s _ = _] |- _ => 
        rewrite H in *; clear H
    end);
    restore_pures; sl_simpl; sl_restore s.

    
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

  Lemma rule_write : forall (x : var) f e e' PP,
    (|= {[ (var_expr x) · `f >> e ]} cwrite x f e' {[ (x:expr) · `f >> e']} @ PP)%spec.
  Proof.
    intros. unfold c_triple. apply all_specEIR. intro sc.
    apply pure_impl_specR. intro Hsemantics.
    inversion Hsemantics. subst. clear Hsemantics.
    intros n PP' HPP _. unfold triple; simpl. introv HPP' Hm Hk [HSub Hnotnull].
    assert (PSM.MapsTo (val_to_ptr (s x), f) (e s) h) as Hh.
    > apply heap_sub_alt in HSub. red in HSub. apply HSub. PSM'.simp. auto.
    clear HSub.
    split.
    > intro Hfail. inversion Hfail. subst. firstorder.
    > introv Hsem. inversion Hsem. subst. split; [|assumption].
      apply heap_sub_alt. unfold PSM'.Sub. PSM'.simp. firstorder.
  Qed.

  Lemma subst_fresh0 (vs: var -> val) :
    subst_fresh vs nil =X= subst0.
  Proof. reflexivity. Qed.
  Hint Rewrite subst_fresh0 : open.

  Lemma rule_write_frame G P Q (x : var) f e e' PP :
    (P |- Q <*> (x:expr) · `f >> e)%asn ->
    (G |= {[ P ]} cwrite x f e' {[ Q <*> (x:expr) · `f >> e']} @ PP)%spec%asn.
  Proof.
    intros HP; rewrite HP.
    sl_rewritel sc_upC. sl_rewriter sc_upC.
    eapply roc_post. eapply rule_frame. rewrite true_specR. apply rule_write.
    sl_tac (apply sc_upME); [reflexivity|].
    unfold subst_mod_asn. simpl. sl_existE vs. 
    unfold SS.MSet.Raw.empty. autorewrite with open.
    unfold_stack s; reflexivity.
  Qed.
  Implicit Arguments rule_write_frame [[G] [P] [Q] [x] [f] [e] [e']].

  Lemma roc_mspec G C m ps P P' Q Q' r PP : (
    P  |- P' ->
    Q' |- Q  ->
    G  |= C :.: m |-> ps {{ P' }}-{{ r, Q' }} @ PP ->
    G  |= C :.: m |-> ps {{ P  }}-{{ r, Q  }} @ PP)%asn%spec.
  Proof.
    intros HPre HPost HMS; rewrite HMS, HPre, HPost; reflexivity.
  Qed.

  (* TODO: fixme (haven't looked, cause it's boring)
  Lemma I_postcond P Q SC c :
    ((|>SC [/\] {[ P ]} c {[ Q ]}) |= {[ P ]} c {[ lift0 (FunI _ SC) </\> Q ]})%asn%spec.
  Proof.
    unfold entails_spec; simpl; intros n [HSC HT]; intros;
      edestruct HT; intuition eauto.
    destruct n.
    > inversion H; subst; inversion H1; subst; inversion H2; subst; clear H H1 H2; simpl in *.
      contradiction (cmd_zero H6).
    eapply spec_dc; [| eassumption].
    destruct k; [contradiction (cmd_zero H6) |].
    omega.
  Qed.
  *)

Lemma triple_exists_elim {A} (P: A -> hasn) c q S PP
  (H: forall x, S |= c_triple (P x) q c @ PP) :
  S |= c_triple (<E>x, P x) q c @ PP.
Proof.
  rewrite <- exists_into_precond_c. spec_all x. apply H.
Qed.

Lemma triple_extract_prop_base p q c (P : pure) S PP
  (H: forall s, P s -> S |= c_triple p q c @ PP) :
  S |= c_triple (p </\> <pure>P) q c @ PP.
Proof.
  intros i PP' HPP HS sc n PQ HPQ Hni Hsem m k PR s h HPR Hmn Hmk [Hp HP]; simpl in *.
  specialize (H s HP i _ HPP HS sc n _ HPQ Hni Hsem m k _ s h HPR Hmn Hmk Hp).
  destruct H as [HSafe HStep].
  split; [assumption | intros h' s'].
  apply HStep.
Qed.

Lemma triple_extract_prop p q c (P Q : pure) S PP
  (H: forall s, P s -> S |= c_triple (p </\> <pure>Q) q c @ PP) :
  S |= c_triple (p </\> <pure>(lift2 and P Q)) q c @ PP.
Proof.
  unfold entails_spec in *; simpl in *; intros.
  eapply H; try eassumption; simpl; intuition; eassumption.
Qed.

(* TODO: figure out how to fix
Definition AsnExtractSpec {S} (G : spec) (p q : asn S) :=  (p </\> lift0 (FunI _ G) -|- q).

Lemma asn_merge_spec {V S} (G H : spec) :
  lift0 (FunI _ G) </\> lift0 (FunI _ H) -|- @lift0 V _ (FunI S (G [/\] H)).
Proof.
  split; intros n; simpl; intros; assumption.
Qed.

Definition SpecCombine G1 G2 := G1 =|= G2. 

Lemma SpecCombineTrueRight G : SpecCombine (G [/\] [true]) G.
Proof.
  unfold SpecCombine. rewrite spec_and_unit_trueL. reflexivity.
Qed.

Lemma SpecCombineTrueLeft G : SpecCombine ([true] [/\] G) G.
Proof.
  unfold SpecCombine. rewrite and_specC, spec_and_unit_trueL. reflexivity.
Qed.

Lemma SpecCombineRefl G : SpecCombine G G.
Proof.
  unfold SpecCombine; reflexivity.
Qed.

Hint Extern 0 (SpecCombine (_ [/\] [true]) _) => simple apply SpecCombineTrueRight : spec_combine_db.
Hint Extern 0 (SpecCombine ([true] [/\] _) _) => simple apply SpecCombineTrueLeft : spec_combine_db.
Hint Extern 10 (SpecCombine _ _) => simple apply SpecCombineRefl : spec_combine_db.
*)
(*End SemRules.

Module Type RULES (P: PROGRAM).
  Include SemRules P.
End RULES.

Module Rules (P: PROGRAM) : RULES P.
  Include SemRules P.
End Rules.*)

Close Scope open_scope.
Close Scope asn_scope.
Close Scope spec_scope.
