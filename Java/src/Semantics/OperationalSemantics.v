Require Import Program SepAlg AssertionLogic SpecLogic SepAlgMap.
Require Import MapInterface MapFacts.
Require Import ILInsts ILogic ILEmbed Open Subst Stack Lang.

Import SepAlgNotations.

Set Implicit Arguments.
Unset Strict Implicit.

Section Commands.

  Definition semCmdType := Prog_wf -> nat -> stack -> heap -> option (stack * heap) -> Prop.
  Definition safe (c : semCmdType) P s t n := ~(c P s t n None).
  Definition frame_property (c : semCmdType) :=
    forall P s s' (big big' frame h : heap) n
      (HFrame : sa_mul h frame big)
      (HSafe  : forall m, m <= n -> safe c P m s h)
      (HSem   : c P n s big (Some (s', big'))),
      exists h', sa_mul h' frame big' /\ c P n s h (Some (s', h')).

  Record semCmd := {
    cmd_rel   :> Prog_wf -> nat -> stack -> heap -> option (stack * heap) -> Prop;
    cmd_zero  :  forall P s h cfg, ~(cmd_rel P 0 s h cfg);
    cmd_frame :  frame_property cmd_rel
  }.

  Definition not_modifies (c : semCmdType) x : Prop :=
    forall P s s' h h' n (HSem : c P n s h (Some (s', h'))),
      s x = s' x.

  Lemma safe_zero : forall (c : semCmd) P s t, safe c P 0 s t.
  Proof.
    intros; apply cmd_zero.
  Qed.

  Global Opaque sa_mul.

  Implicit Arguments Build_semCmd [].

  Program Definition later_cmd (c : semCmd) : semCmd := Build_semCmd
    (fun P n => match n return stack -> heap -> option (stack * heap) -> Prop with
                  | O => fun _ _ _ => False
                  | S n => c P n end) _ _.
  Next Obligation.
    unfold frame_property; intros.
    destruct n as [| n]; unfold safe in HSafe; simpl in *; [contradiction |].
    eapply cmd_frame; eauto. 
    intros m HLe HFail; apply (HSafe (S m)); auto with arith.
  Qed.

  (* Skip *)

  Inductive skip_sem : semCmdType :=
  | s_ok : forall P s h, skip_sem P 1 s h (Some (s, h)).
  Program Definition skip_cmd := @Build_semCmd skip_sem _ _.
  Next Obligation.
    intros H. inversion H.
  Qed.
  Next Obligation.
    unfold frame_property; intros.
    inversion HSem; subst; clear HSem.
    exists h; auto using skip_sem.
  Qed.

  (* Seq *)
  Inductive seq_sem (c1 c2 : semCmd) : semCmdType :=
  | seq_failL : forall P n s h,
      c1 P n s h None ->
      seq_sem c1 c2 P (S n) s h None
  | seq_failR : forall P n n' s s' h h',
      c1 P n s h (Some (s', h')) ->
      c2 P n' s' h' None ->
      seq_sem c1 c2 P (S (n + n')) s h None
  | seq_ok    : forall P n n0 s s0 s1 h h0 h1,
      c1 P n  s  h  (Some (s0, h0)) ->
      c2 P n0 s0 h0 (Some (s1, h1)) ->
      seq_sem c1 c2 P (S (n + n0)) s h (Some (s1, h1)).
  Program Definition seq_cmd c1 c2 := @Build_semCmd (seq_sem c1 c2) _ _.
  Next Obligation.
    intros H; inversion H.
  Qed.
  Next Obligation with eauto using seq_sem.
    unfold frame_property; intros.
    inversion HSem; subst; clear HSem.
    edestruct (@cmd_frame c1) as [h0 [HFrame0 HSem0]]...
    + intros m HLe HFail; apply HSafe with (S m); [omega | ]...
    + edestruct (@cmd_frame c2) as [hr [HFrame1 HSem1]]...
      intros m HLe HFail; apply HSafe with (S (n0 + m)); [omega | ]...
  Qed.

  (* Nondet *)
  Inductive nondet_sem (c1 c2 : semCmd) : semCmdType :=
  | nondet_failL : forall P n s h,
      c1 P n s h None ->
      nondet_sem c1 c2 P (S n) s h None
  | nondet_okL   : forall P n s s' h h',
      c1 P n s h (Some (s', h')) ->
      nondet_sem c1 c2 P (S n) s h (Some (s', h'))
  | nondet_failR : forall P n s h,
      c2 P n s h None ->
      nondet_sem c1 c2 P (S n) s h None
  | nondet_okR   : forall P n s s' h h',
      c2 P n s h (Some (s', h')) ->
      nondet_sem c1 c2 P (S n) s h (Some (s', h')).
  Program Definition nondet_cmd c1 c2 := @Build_semCmd (nondet_sem c1 c2) _ _.
  Next Obligation.
    intros H; inversion H.
  Qed.
  Next Obligation with eauto using nondet_sem.
    unfold frame_property; intros.
    inversion HSem; subst; clear HSem.
    + edestruct (@cmd_frame c1) as [h0 [HFrame0 HSem0]]...
      intros m HLe HFail; apply HSafe with (S m); [omega |]...
    + edestruct (@cmd_frame c2) as [h0 [HFrame0 HSem0]]...
      intros m HLe HFail; apply HSafe with (S m); [omega |]...
  Qed.

  (* Kleene star *)
  Inductive kleene_sem (c : semCmd) : semCmdType :=
  | kleene_emp       : forall P s h,
      kleene_sem c P 1 s h (Some (s, h))
  | kleene_fail_one  : forall P n s h,
      c P n s h None ->
      kleene_sem c P (S n) s h None
  | kleene_fail_many : forall P n n0 s s0 h h0,
      c P n s h (Some (s0, h0)) ->
      kleene_sem c P n0 s0 h0 None ->
      kleene_sem c P (S (n + n0)) s h None
  | kleene_step_ok   : forall P n n0 s s0 s1 h h0 h1,
      c P n s h (Some (s0, h0)) ->
      kleene_sem c P n0 s0 h0 (Some (s1, h1)) ->
      kleene_sem c P (S (n + n0)) s h (Some (s1, h1)).
  Program Definition kleene_cmd c := @Build_semCmd (kleene_sem c) _ _.
  Next Obligation.
    intros H; inversion H.
  Qed.
  Next Obligation with eauto using kleene_sem.
    unfold frame_property; intros.
    generalize dependent h; remember (Some (s', big')) as cfg; induction HSem;
      inversion Heqcfg; subst; intros; clear Heqcfg...
    edestruct (@cmd_frame c) as [h' [HFrame0 HSem0]]...
    + intros m HLe HFail; apply HSafe with (S m); [omega |]...
    + destruct (IHHSem (eq_refl _) h' HFrame0) as [hr [HFrame1 HSem1]]...
      intros m HLe HFail; apply HSafe with (S (n + m)); [omega |]...
  Qed.

  (* TODO: update the description
     assume command -- this command is a bit of a hack that just skips if
     a check holds and loops otherwise, this way allowing to encode if/while
     using nondeterministic choice/Kleene star *)
  Inductive assume_sem (e : dexpr) : semCmdType :=
  | assume_ok : forall P s h, eval e s = vbool true -> assume_sem e P 1 s h (Some (s, h)).
  Program Definition assume_cmd P := @Build_semCmd (assume_sem P) _ _.
  Next Obligation.
    intros H; inversion H.
  Qed.
  Next Obligation.
    unfold frame_property; simpl; intros.
    remember (Some (s', big')) as cfg; induction HSem.
    inversion Heqcfg; subst; eauto using assume_sem.
  Qed.

  Lemma assume_inv P e n s s0 h h0 (HSem : assume_cmd e P n s h (Some (s0, h0))) : 
      s = s0 /\ h = h0.
  Proof.  
    intros; remember (Some (s0, h0)); induction HSem; subst;
    try inversion Heqo; intuition.
  Qed.

  Inductive assert_sem (e : dexpr) : semCmdType :=
  | assert_ok   : forall P s h (HP : eval e s = vbool true),
    assert_sem e P 1 s h (Some (s, h))
  | assert_fail : forall P s h (HNP : eval e s = vbool false),
    assert_sem e P 1 s h None.
  Program Definition assert_cmd e := @Build_semCmd (assert_sem e) _ _.
  Next Obligation.
    intros H; inversion H.
  Qed.
  Next Obligation.
    unfold frame_property; simpl; intros.
    inversion HSem; subst; eauto using assert_sem.
  Qed.  

  Inductive assign_sem (x : var) (e : dexpr) : semCmdType :=
  | assign_ok : forall P s h v
                       (He: eval e s = v),
      assign_sem x e P 1 s h (Some (stack_add x v s, h))
  | assign_fail : forall P s h
                    (He: eval e s = nothing),
    assign_sem x e P 1 s h None.
  Program Definition assign_cmd x e := Build_semCmd (assign_sem x e) _ _.
  Next Obligation.
    intros H; inversion H.
  Qed.
  Next Obligation with eauto using assign_sem.
    unfold frame_property; intros.
    inversion HSem; subst; clear HSem; exists h...
  Qed.

  Inductive read_sem (x y : var) (f : field) : semCmdType :=
  | read_ok : forall ref v P (s : stack) (h : heap)
      (Rref  : s y = vptr ref)
      (Rmaps : MapsTo (ref,f) v h),
      read_sem x y f P 1 s h (Some (stack_add x v s, h))
  | read_fail : forall ref P s h
      (Sref   : s y = vptr ref)
      (Snotin : ~ In (ref,f) h ),
      read_sem x y f P 1 s h None.
  Program Definition read_cmd x y f := Build_semCmd (read_sem x y f) _ _.
  Next Obligation.
    intros H; inversion H.
  Qed.
  Next Obligation with eauto using read_sem.
    unfold frame_property; intros.
    inversion HSem; subst n s0 h0 s' big'; clear HSem; exists h; intuition.
    apply read_ok with ref; [assumption |]; specialize (HSafe _ (le_n _)).
    destruct (sa_mul_mapstoR HFrame Rmaps) as [[H1 H2] | [H1 H2]]; [assumption|].
    contradiction HSafe; apply read_fail with ref; [assumption |].
    intro HIn. apply H2. assumption.
  Qed.

  Inductive alloc_sem (x : var) (C : class) : semCmdType :=
  | alloc_ok : forall (P : Prog_wf) (s s0 : stack) (h h0 : heap) n fields
      (Snotnull : (n, C) <> pnull)
(*      (Seq      : val_class ref = C)*)
      (Sfresh_h : forall f, ~ In ((n, C), f) h)
      (Sfields  : field_lookup P C fields)
      (Sh0      : sa_mul h
        (SS.fold (fun f h' => add ((n, C), f) (pnull : val) h') fields heap_unit) h0)
      (Ss0      : s0 = stack_add x (vptr (n, C)) s),
      alloc_sem x C P 1 s h (Some (s0, h0)).
  Program Definition alloc_cmd x C := Build_semCmd (alloc_sem x C) _ _.
  Next Obligation.
    intros H; inversion H.
  Qed.
  Next Obligation.
    unfold frame_property; intros.
    inversion HSem; subst n s0 h0 s' big'; clear HSem.
    destruct (sa_mulA HFrame Sh0) as [h2 [H1 H2]].
    apply sa_mulC in H2; destruct (sa_mulA H1 H2) as [h3 [H3 H5]].
    exists h3.
    split; [apply sa_mulC; assumption|].
    eapply alloc_ok; [eassumption | | eassumption | apply sa_mulC; assumption | reflexivity].
    intros f H6; apply (Sfresh_h f).
    apply sa_mulC in H2; destruct (sa_mul_inL H2 H6) as [H7 H8].
    destruct (sa_mul_inR Sh0 H8) as [[H9 H10] | [H9 H10]]; [assumption|].
    apply sa_mulC in H1; destruct (sa_mul_inL H1 H9); intuition.
  Qed.

  Inductive write_sem (x:var) (f:field) (e:dexpr) : semCmdType := 
  | write_ok : forall P (s: stack) h h' ref v
      (Sref: s x = vptr ref)
      (Sin:  In (ref,f) h )
      (Heval : eval e s = v)
      (Sadd: h' = add (ref,f) v h ),
      write_sem x f e P 1 s h (Some (s, h'))
  | write_fail : forall P (s: stack) h ref
      (Sref:   s x = vptr ref)
      (Sin : ~ In (ref, f) h),
      write_sem x f e P 1 s h None.
  Program Definition write_cmd x f e := Build_semCmd (write_sem x f e) _ _.
  Next Obligation.
    intros H; inversion H.
  Qed.
  Next Obligation.
    unfold frame_property; intros.
    inversion HSem. subst; clear HSem.
    assert (~ In (ref, f) frame).
    intros H. 
    apply (HSafe 1); [omega |].
    eapply write_fail; [eassumption|].
    destruct (sa_mul_inR HFrame Sin); intuition.
    exists (add (ref, f) (eval e s') h). split.
    apply sa_mul_add; assumption.
    eapply write_ok; try eassumption; try reflexivity.
    destruct (sa_mul_inR HFrame Sin); intuition.
  Qed.

  Fixpoint create_stack (ps : list var) (vs : list val) : stack :=
    match ps, vs with
      | nil, nil => stack_empty var
      | p :: ps, v :: vs =>
        stack_add p v (create_stack ps vs)
      | _, _ => stack_empty var
    end.
        
  Inductive call_sem (rvar : var) (C : open class) m es (c : cmd) (sc : semCmd)
    : semCmdType :=
  | call_failS : forall (P : Prog_wf) s h
      (HLFail  : forall mrec, ~ method_lookup P (C s) m mrec),
      call_sem rvar C m es c sc P 1 s h None
  | call_failC : forall (P : Prog_wf) ps rexpr (s : stack) h n
      (HLookup : method_lookup P (C s) m (Build_Method ps c rexpr))
      (HLen    : length ps = length es)
      (HFail   : sc P n (create_stack ps (eval_exprs s es)) h None),
      call_sem rvar C m es c sc P (S n) s h None
  | call_failL : forall (P : Prog_wf) ps rexpr s h
      (HLookup : method_lookup P (C s) m (Build_Method ps c rexpr))
      (HLen    : length ps <> length es),
      call_sem rvar C m es c sc P 1 s h None
  | call_ok    : forall (P : Prog_wf) ps rexpr (s sr : stack) h hr n
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
  | semskip   : semantics cskip skip_cmd
  | semseq    : forall c1 c2 sc1 sc2
      (HL : semantics c1 sc1)
      (HR : semantics c2 sc2),
      semantics (cseq c1 c2) (seq_cmd sc1 sc2)
  | semif     : forall e cl cr scl scr
      (HL : semantics cl scl)
      (HR : semantics cr scr),
      semantics (cif e cl cr) (nondet_cmd
        (seq_cmd (assume_cmd e) scl)
        (seq_cmd (assume_cmd (E_not e)) scr))
  | semwhile  : forall e c sc
      (HS : semantics c sc),
      semantics (cwhile e c) (seq_cmd (kleene_cmd
        (seq_cmd (assume_cmd e) sc)) (assume_cmd (E_not e)))
  | semdcall  : forall (x y : var) m es c sc 
      (HSem     : semantics c sc),
      semantics (cdcall x y m es) (call_cmd x ((liftn val_class) (var_expr y)) m ((E_var y) :: es) c sc)
  | semscall  : forall (x : var) (C : class) m es c sc
      (HSem     : semantics c sc),
      semantics (cscall x C m es) (call_cmd x (open_const C) m es c sc)
  | semassert : forall e,
      semantics (cassert e) (assert_cmd e).

  Definition c_not_modifies c x :=
    forall sc, semantics c sc -> not_modifies sc x.

  Lemma modifies_syn_sem c x :
     ~ SS.In x (modifies c) -> c_not_modifies c x.
  Proof.
    induction c; simpl in *; intros HNM; intros sc HSem; inversion_clear HSem.
    + rewrite SS'.singleton_iff in HNM; intros P s s0 h h0 n HAsgn;
      simpl in *; inversion HAsgn; subst.
      rewrite stack_lookup_add2; trivial.
    + intros P s s0 h h0 n HSkip; simpl in *; inversion HSkip; subst; trivial.
    + intros P s s0 h h0 n HSeq; simpl in *; inversion HSeq; subst.
      transitivity (s2 x).
      * eapply IHc1; [| eassumption | eassumption]; intros HIn; apply HNM;
        rewrite SS'.union_iff; auto.
      * eapply IHc2; [| eassumption | eassumption]; intros HIn; apply HNM;
        rewrite SS'.union_iff; auto.
    + intros P s s0 h h0 n HND; simpl in *; inversion HND; subst; clear HND.
      * inversion H4; subst.
        apply assume_inv in H6; destruct H6; subst.
        eapply IHc1; [| eassumption | eassumption]; intros HIn; apply HNM;
          rewrite SS'.union_iff; auto.
      * inversion H4; subst.
        apply assume_inv in H6; destruct H6; subst.
        eapply IHc2; [| eassumption | eassumption]; intros HIn; apply HNM;
        rewrite SS'.union_iff; auto.
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
    + rewrite SS'.singleton_iff in HNM; intros P s s0 h h0 n HRd; simpl in *;
      inversion HRd; subst; rewrite stack_lookup_add2; trivial.
    + rewrite SS'.singleton_iff in HNM; intros P s s0 h h0 n HCl; simpl in *;
      inversion HCl; subst; rewrite stack_lookup_add2; trivial.
    + rewrite SS'.singleton_iff in HNM; intros P s s0 h h0 n HCl; simpl in *;
      inversion HCl; subst; rewrite stack_lookup_add2; trivial.
    + rewrite SS'.singleton_iff in HNM; intros P s s0 h h0 n HCl; simpl in *;
      inversion HCl; subst; rewrite stack_lookup_add2; trivial.
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

  Program Definition triple_aux (p q : sasn) (c : semCmd) : spec :=
    mk_spec (fun n P => forall P' m k s h, Prog_wf_sub P P' -> m <= n -> k <= m -> 
                                           p s P' m h ->
      safe c P' k s h /\
      forall h' s', c P' k s h (Some (s', h')) -> (q s' P' (m - k) h')) _ _.
  Next Obligation.
    apply H0; try eassumption.
    etransitivity; eassumption.
  Qed.

  Local Transparent ILPre_Ops.
  Local Transparent ILFun_Ops.

  Add Parametric Morphism : triple_aux with signature
    lentails --> lentails ++> eq ==> lentails
    as triple_aux_entails_m.
  Proof.
    intros p p' Hp q q' Hq c n t H P m k s h HP Hmn Hkm Hp'.
    apply Hp in Hp'; try apply _.    
    simpl in *.
    specialize (H _ _ _ _ _ HP Hmn Hkm Hp').
    destruct H as [Hsafe H].
    split; [assumption|].
    intros h' s' Hc.
    apply Hq.
    apply H. assumption.
  Qed.

  Add Parametric Morphism : triple_aux with signature
    lequiv ==> lequiv ==> eq ==> lequiv
    as triple_aux_lequiv_m.
  Proof.
    split.
    + rewrite H, H0; reflexivity.
    + rewrite <- H, <- H0; reflexivity.
  Qed.

  Definition triple (P Q : sasn) (c : cmd) :=
    Forall sc : semCmd, (semantics c sc) ->> triple_aux P Q sc.

  Notation " '{[' P ']}' c '{[' Q ']}' " := (triple P Q c) (at level 89,
    format " {[ P ]} '/' c '/' {[ Q ]} ").

Open Scope open_scope.

  Definition method_spec C m (ps : list var) (rn : var) (P Q : sasn) := (
    NoDup (rn :: ps) /\\
    Exists ps' : (list var), Exists c : cmd, Exists re : dexpr,
      [prog] (fun X : Prog_wf => method_lookup X C m (Build_Method ps' c re)
        /\ length ps = length ps' /\
        (forall x, List.In x ps' -> ~ SS.In x (modifies c)))
      //\\ {[ P //! zip ps (List.map var_expr ps') ]}
         c {[ Q //! zip (rn :: ps) (eval re :: (List.map var_expr ps'))]}
    ).

  Notation " C ':.:' m |-> ps {{ P }}-{{ r , Q }} " :=
    (method_spec C m ps r P Q) (at level 60).

  Lemma c_triple_zero P (p q : sasn) (c : cmd) :
    ({[ p ]} c {[ q ]}) 0 P.
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