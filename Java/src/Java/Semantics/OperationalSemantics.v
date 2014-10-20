Require Import Program SepAlg SepAlgInsts AssertionLogic SpecLogic SepAlgMap.
Require Import MapInterface MapFacts.
Require Import ILInsts ILogic ILEmbed ILEmbedTac ILQuantTac OpenILogic 
        Open Subst Stack Lang HeapArr BILogic.

Import SepAlgNotations.

Set Implicit Arguments.
Unset Strict Implicit.

Section Commands.

  Variable (P : Program).

   Inductive sem_cmd : stack -> heap -> cmd -> option (stack * heap * cmd) -> Prop :=
	| sem_seq_fail s h c1 c2 : sem_cmd s h c1 None -> sem_cmd s h (cseq c1 c2) None
  	| sem_seq_skip s h c : sem_cmd s h (cseq cskip c) (Some (s, h, c))
  	| sem_seq_step s h s' h' c1 c1' c2 : 
  		sem_cmd s h c1 (Some (s', h', c1')) ->
  		sem_cmd s h (cseq c1 c2) (Some (s', h', cseq c1' c2))
  		
    | sem_assign s h x v e : 
    	eval e s = v ->
    	sem_cmd s h (cassign x e) (Some (stack_add x v s, h, cskip))
    
    | sem_read_fail (ref : ptr) x y f ref (s : stack) (h : heap_ptr) h' :
        s y = vptr ref ->
        ~ In (ref, f) h ->
        sem_cmd s (h, h') (cread x y f) None
    | sem_read (ref : ptr) x y f ref v (s : stack) (h : heap) :
        s y = vptr ref ->
        MapsTo (ref, f) v (fst h) ->
        sem_cmd s h (cread x y f) (Some (stack_add x v s, h, cskip))
        
    | sem_write_fail x f e s h h' ref :
        s x = vptr ref ->
        ~ In (ref, f) h ->
        sem_cmd s (h, h') (cwrite x f e) None
    | sem_write x f e s h h' h'' ref v :
      s x = vptr ref ->
      In (ref, f) h ->
      eval e s = v ->
      add (ref, f) v h = h' ->
      sem_cmd s (h, h'') (cwrite x f e) (Some (s, (h', h''), cskip))
        
    | sem_alloc x C s s' h h' h'' n fields :
    	(n, C) <> pnull ->
    	(forall f, ~ In ((n, C), f) h) ->
    	field_lookup P C fields ->
    	sa_mul h
          (fold_right (fun f h' => add ((n, C), f) (pnull : val) h') heap_ptr_unit fields) h' ->
    	s' = stack_add x (vptr (n, C)) s ->
    	sem_cmd s (h, h'') (calloc x C) (Some (s', (h', h''), cskip)).

  Inductive run : stack -> heap -> cmd -> nat -> stack -> heap -> Prop :=
  	| run_skip s h n : run s h cskip n s h
  	| run_step n s h c s' h' c' s'' h'' : 
  		sem_cmd s h c (Some (s', h', c')) ->
  		run s' h' c' n s'' h'' ->
  		run s h c (S n) s'' h''.
  
  Program Definition safe (c : cmd) : spec :=
  	mk_spec (fun Pr n P => forall s h m, P s h -> n >= m -> exists s' h', run s h c n s' h') _ _ _.
  Next Obligation.
	assert (S k >= m) by omega.
	destruct (H _ _ _ H0 H2) as [s' [h' HR]].
    admit.
  Qed.
  Next Obligation.
	Require Import BILInsts IBILogic.
	Transparent SAIBIOps BILFun_Ops.
	unfold extSP in H.
	destruct H as [R [_ H]].
	specialize (H _ _ H1); simpl in H.
	Transparent BILogicOpsAsn.
	Transparent ILogicOps_Prop. simpl in *.
	unfold sepSP in H. simpl in H.
	unfold ILPreFrm_pred in H. simpl in *.
	unfold ILPreFrm_pred in H.
	unfold sepSP in H.
	re
	Transparent Build_BILOperators.
	unfold Build_BILOperators in H.
	Transparent mkILPreFrm.
	unfold mkILPreFrm in H.
	simpl in H.
destruct H.
  Fixpoint create_stack (ps : list var) (vs : list val) : stack :=
    match ps, vs with
      | nil, nil => stack_empty var val
      | p :: ps, v :: vs =>
        stack_add p v (create_stack ps vs)
      | _, _ => stack_empty var val
    end.
        
  Inductive call_sem (rvar : var) (C : open class) m es (c : cmd) (sc : semCmd)
    : semCmdType :=
  | call_failS : forall (P : Program) s h
      (HLFail  : forall mrec, ~ method_lookup P (C s) m mrec),
      call_sem rvar C m es c sc P 1 s h None
  | call_failC : forall (P : Program) ps rexpr (s : stack) h n
      (HLookup : method_lookup P (C s) m (Build_Method ps c rexpr))
      (HLen    : length ps = length es)
      (HFail   : sc P n (create_stack ps (eval_exprs s es)) h None),
      call_sem rvar C m es c sc P (S n) s h None
  | call_failL : forall (P : Program) ps rexpr s h
      (HLookup : method_lookup P (C s) m (Build_Method ps c rexpr))
      (HLen    : length ps <> length es),
      call_sem rvar C m es c sc P 1 s h None
  | call_ok    : forall (P : Program) ps rexpr (s sr : stack) h hr n
      (HLookup : method_lookup P (C s) m (Build_Method ps c rexpr))
      (HLen    : length ps = length es)
      (HSem    : sc P n (create_stack ps (eval_exprs s es)) h (Some (sr, hr))),
      call_sem rvar C m es c sc P (S n) s h
        (Some (stack_add rvar (eval rexpr sr) s, hr)).
  Program Definition call_cmd rvar C m es c sc := Build_semCmd (call_sem rvar C m es c sc) _ _.
  Next Obligation.
    intros H; inversion H.
  Qed.
  Next Obligation with eauto using call_sem.
    unfold frame_property; intros.
    inversion HSem; subst; clear HSem.
    edestruct (@cmd_frame sc) as [h1 [HFrame1 HSem1]]...
    intros k HLe HFail; apply HSafe with (S k); [omega |]...
  Qed.

  Inductive semantics : cmd -> semCmd -> Prop :=
  | semassign : forall x e,
      semantics (cassign x e) (assign_cmd x e)
  | semread   : forall x y f,
      semantics (cread x y f) (read_cmd x y f)
  | semalloc  : forall x C,
      semantics (calloc x C) (alloc_cmd x C)
  | semwrite  : forall x f e,
      semantics (cwrite x f e) (write_cmd x f e)
  | semarrread : forall x y es,
                   semantics (carrread x y es) (read_arr_cmd x y es)
  | semarrwrite : forall x es e,
                   semantics (carrwrite x es e) (write_arr_cmd x es e)
  | semarralloc : forall x (e : dexpr),
                    semantics (carralloc x e) (alloc_arr_cmd x e)
  | semskip   : semantics cskip skip_cmd
  | semseq    : forall c1 c2 sc1 sc2
      (HL : semantics c1 sc1)
      (HR : semantics c2 sc2),
      semantics (cseq c1 c2) (seq_cmd sc1 sc2)
  | semif     : forall e cl cr scl scr
      (HL : semantics cl scl)
      (HR : semantics cr scr),
      semantics (cif e cl cr) (nondet_cmd
        (seq_cmd (assume_cmd (vlogic_eval e)) scl)
        (seq_cmd (assume_cmd (vlogic_eval (E_not e))) scr))
  | semwhile  : forall e c sc
      (HS : semantics c sc),
      semantics (cwhile e c) (seq_cmd (kleene_cmd
        (seq_cmd (assume_cmd (vlogic_eval e)) sc)) (assume_cmd (vlogic_eval (E_not e))))
  | semdcall  : forall (x y : var) m es c sc 
      (HSem     : semantics c sc),
      semantics (cdcall x y m es) (call_cmd x ((liftn val_class) (var_expr y)) m ((E_var y) :: es) c sc)
  | semscall  : forall (x : var) (C : class) m es c sc
      (HSem     : semantics c sc),
      semantics (cscall x C m es) (call_cmd x (open_const C) m es c sc)
  | semassert : forall e,
      semantics (cassert e) (assert_cmd (vlogic_eval e)).

  Definition c_not_modifies c x :=
    forall sc, semantics c sc -> not_modifies sc x.

  Lemma modifies_syn_sem c x :
     ~ List.In x (modifies c) -> c_not_modifies c x.
  Proof.
    induction c; simpl in *; intros HNM; intros sc HSem; inversion_clear HSem.
    + intros P s s0 h h0 n HAsgn;
      simpl in *; inversion HAsgn; subst.
      rewrite stack_lookup_add2; trivial.
      intuition congruence.
    + intros P s s0 h h0 n HSkip; simpl in *; inversion HSkip; subst; trivial.
    + intros P s s0 h h0 n HSeq; simpl in *; inversion HSeq; subst.
      transitivity (s2 x).
      * eapply IHc1; [| eassumption | eassumption]; intros HIn; apply HNM;
        rewrite in_app_iff; auto.
      * eapply IHc2; [| eassumption | eassumption]; intros HIn; apply HNM;
        rewrite in_app_iff; auto.
    + intros P s s0 h h0 n HND; simpl in *; inversion HND; subst; clear HND.
      * inversion H4; subst.
        apply assume_inv in H6; destruct H6; subst.
        eapply IHc1; [| eassumption | eassumption]; intros HIn; apply HNM;
          rewrite in_app_iff; auto.
      * inversion H4; subst.
        apply assume_inv in H6; destruct H6; subst.
        eapply IHc2; [| eassumption | eassumption]; intros HIn; apply HNM;
        rewrite in_app_iff; auto.
    + intros P s s0 h h0 n HKl; simpl in *; inversion HKl; subst; clear HKl.
      apply assume_inv in H6; destruct H6; subst; simpl in *.
      remember (Some (s0, h0)); induction H5; subst;
        [inversion Heqo; trivial | discriminate | discriminate |].
      transitivity (s1 x); simpl in *.
      * inversion H; subst; clear H.
        apply assume_inv in H7; destruct H7; subst.
        eapply IHc; eassumption.
      * apply IHkleene_sem; assumption.
    + intros P s s0 h h0 n HWr; simpl in *; inversion HWr; subst; reflexivity.
    + intros P s s0 h h0 n HRd; simpl in *;
      inversion HRd; subst; rewrite stack_lookup_add2; trivial;
      intuition congruence.
    + intros P s s0 h h0 n Hrd; simpl in *.
      inversion Hrd; subst. rewrite stack_lookup_add2; [reflexivity | intuition congruence ].
    + intros P s s0 h h0 n Hrd; simpl in *; inversion Hrd; reflexivity.
    + intros P s s0 h h0 n Hrd; simpl in *.
      inversion Hrd; subst. rewrite stack_lookup_add2; [reflexivity | intuition congruence].
    + intros P s s0 h h0 n HCl; simpl in *;
      inversion HCl; subst; rewrite stack_lookup_add2; trivial;
      intuition congruence.
    + intros P s s0 h h0 n HCl; simpl in *;
      inversion HCl; subst; rewrite stack_lookup_add2; trivial;
      intuition congruence.
    + intros P s s0 h h0 n HCl; simpl in *;
      inversion HCl; subst; rewrite stack_lookup_add2; trivial;
      intuition congruence.
    + intros P s s0 h h0 n HAs; inversion HAs; subst; reflexivity.
  Qed.

  (* A reasonable alternative definition would be
   * [ [E] sc, [pure] semantics c sc [/\] triple _ P Q sc ]
   *
   * The two definitions should really be equivalent, but proving that to be
   * the case requires proving that [semantics] is a total and functional
   * relation. This might not be straightforward since it requires induction
   * over some number of steps, either by indexing [semantics] with [nat] or by
   * somehow using the number that's in the semCmd parameter.
   *
   * The definition chosen here allows us to lift all the proof rules about
   * triples that we care about into c_triple. The proof rules that cannot be
   * lifted here but could be lifted with the other definition seem to be more
   * obscure. For example, {true} c {true} |= [E]s,[E]h, safe c s h. Here, the
   * witness for the existential depends on the triple, but the triple cannot
   * be taken apart without guessing a semantic command.
   *)

End Commands.

  Local Transparent ILPre_Ops.
  Local Transparent ILFun_Ops.

  Definition triple (P Q : sasn) (c : cmd) :=
    Forall sc : semCmd, (semantics c sc) ->> {{P}} sc {{Q}}.

  Notation " '{[' P ']}' c '{[' Q ']}' " := (triple P Q c) (at level 89,
    format " {[ P ]} '/' c '/' {[ Q ]} ").

  Add Parametric Morphism : triple with signature
    lentails --> lentails ++> eq ==> lentails
    as triple_entails_m.
  Proof.
    intros p p' Hp q q' Hq c.
    unfold triple. 
    setoid_rewrite Hq; setoid_rewrite <- Hp. reflexivity.
  Qed.

Open Scope open_scope.

  Definition method_spec C m (ps : list var) (rn : var) (P Q : sasn) := (
    NoDup (rn :: ps) /\\
    Exists ps' : (list var), Exists c : cmd, Exists re : dexpr,
      [prog] (fun X : Program => method_lookup X C m (Build_Method ps' c re)
        /\ length ps = length ps' /\
        (forall x, List.In x ps' -> ~ List.In x (modifies c)))
      //\\ {[ P //! zip ps (List.map var_expr ps') ]}
         c {[ Q //! zip (rn :: ps) (eval re :: (List.map var_expr ps'))]}
    ).

  Notation " C ':.:' m |-> ps {{ P }}-{{ r , Q }} " :=
    (method_spec C m ps r P Q) (at level 60).

  Add Parametric Morphism : method_spec with signature
    eq ==> eq ==> eq ==> eq ==>
      lentails --> lentails ++> lentails
    as method_spec_entails_m.
  Proof.
    intros C m ps rn P P' HP Q Q' HQ. unfold method_spec.
    (* Unravel the two almost identical sides of the entailment first because
        setoid_rewrite doesn't seem to go under these binders. *)
    apply lpropandL; intro H. apply lpropandR; [assumption|].
    lexistsL ps' c re. lexistsR ps' c re.
    apply landR; [apply landL1; reflexivity | apply landL2].
    admit.
(*    setoid_rewrite HP. setoid_rewrite HQ. reflexivity.*)
  Qed.

  Add Parametric Morphism : method_spec with signature
    eq ==> eq ==> eq ==> eq ==>
      lequiv ==> lequiv ==> lequiv
    as method_spec_bientails_m.
  Proof.
    split; apply method_spec_entails_m; try rewrite ?H, ?H0; reflexivity.
  Qed.


  Lemma c_triple_zero P (p q : sasn) (c : cmd) :
    ({[ p ]} c {[ q ]}) P 0.
  Proof.
    intros sc n Hn Q HPQ sem R k m s h HQR Hk Hv Hp.
    assert (m = 0) by omega.
    assert (k = 0) by omega.
    subst. split.
    + apply safe_zero.
    + intros h' s'' Hc. apply cmd_zero in Hc. contradiction.
  Qed.

(* Arguments swapped to please the type classes *)

  Definition typeof (C : class) (v : val) : Prop := exists p, v = vptr p /\ snd p = C.
(*
  Notation " x ':::' C " := 
    (@coerce _ _ (@lift2_C _ _ _ _) typeof (@coerce _ _ (@lift0_C _ _) C) (var_expr x)) (at level 60).

  (* TODO: should P,Q be allowed to reference stack vars from the outside? *)
  Definition expr_spec x m (ps: list var) (r: var) (P Q: hasn) : hasn :=
    (<E> C, <pure> x:::C </\> lift0 (FunI (C:.:m |-> ps {{P}}-{{r,Q}})))
    %asn.

  Arguments Scope expr_spec [_ _ _ _ asn_scope asn_scope].

  Notation " x ':..:' m |-> ps {{ P }}-{{ r , Q }} " :=
    (expr_spec x m ps r P Q) (at level 60).
*)

Section StructuralRules.

  Lemma triple_false (G : spec) (Q : sasn) c :
    G |-- {[lfalse]} c {[Q]}.
  Proof.
    intros n; simpl in *; intros; destruct H4.
  Qed.

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
  
  Lemma rule_frame_ax_list P Q R c (xs: list var)
    (HMod : forall x, ~ List.In x xs -> c_not_modifies c x) :
    {[ P ]} c {[ Q ]} |--
    {[ P ** R ]} c {[ Q ** Exists vs, apply_subst R (subst_fresh vs xs) ]}.
  Proof.
    unfold triple. lforallR sc; apply lpropimplR; intro Hsc. lforallL sc. 
    apply lpropimplL; [assumption|].
    apply frame_rule. unfold c_not_modifies in HMod. intros. apply HMod; auto.
  Qed.

  Definition subst_mod_asn (R: sasn) (c: cmd) : sasn :=
    Exists vs, apply_subst R (subst_fresh vs (modifies c)).

  Lemma rule_frame_ax P Q R c : 
    {[ P ]} c {[ Q ]} |--
    {[ P ** R ]} c {[ Q ** subst_mod_asn R c ]}.
  Proof.
    apply rule_frame_ax_list. intros x HnotIn. apply modifies_syn_sem.
    assumption.
  Qed.

  Lemma rule_frame P Q R c G 
    (HPre : G |-- {[P]} c {[Q]}) :
    G |-- {[ P ** R ]} c {[ Q ** subst_mod_asn R c ]}.
  Proof.
    intros; rewrite <- rule_frame_ax; assumption.
  Qed.
  Implicit Arguments rule_frame [[P] [Q] [R] [c] [G]].

  Lemma exists_into_precond2 {A} (P: A -> sasn) c q :
    (Forall x, {[P x]} c {[q]}) -|- {[Exists x, P x]} c {[q]}.
  Proof.
    unfold triple; setoid_rewrite <- exists_into_precond; split.
    + lforallR sc. apply lpropimplR; intro Hsc; lforallR x.
      lforallL x sc. apply lpropimplL; [assumption | reflexivity].
    + lforallR x sc. apply lpropimplR; intro Hsc.
      lforallL sc. apply lpropimplL; [assumption | lforallL x; reflexivity].
  Qed.
  
  Lemma existentialise_triple (x : var) (P Q : sasn) c (G : spec) 
	(H : forall (v : val), G |-- {[@lembedand vlogic sasn _ _ (open_eq (x/V) (`v)) P]} c {[Q]}) :
    G |-- {[P]} c {[Q]}.
  Proof.
    eapply roc_pre; [apply existentialise_var with (x0 := x)|].
    rewrite <- exists_into_precond2. lforallR y. apply H.
  Qed.

End StructuralRules.