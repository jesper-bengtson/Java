Require Import Program SepAlg AssertionLogic SpecLogic SepAlgMap.
Require Import MapInterface MapFacts.
Require Import ILInsts ILogic ILEmbed Open Subst Stack Lang SemCmd.

Import SepAlgNotations.

Set Implicit Arguments.
Unset Strict Implicit.

Section Commands.

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
        (seq_cmd (assume_cmd (pure_eval e)) scl)
        (seq_cmd (assume_cmd (pure_eval (E_not e))) scr))
  | semwhile  : forall e c sc
      (HS : semantics c sc),
      semantics (cwhile e c) (seq_cmd (kleene_cmd
        (seq_cmd (assume_cmd (pure_eval e)) sc)) (assume_cmd (pure_eval (E_not e))))
  | semdcall  : forall (x y : var) m es c sc 
      (HSem     : semantics c sc),
      semantics (cdcall x y m es) (call_cmd x ((liftn val_class) (var_expr y)) m ((E_var y) :: es) c sc)
  | semscall  : forall (x : var) (C : class) m es c sc
      (HSem     : semantics c sc),
      semantics (cscall x C m es) (call_cmd x (open_const C) m es c sc)
  | semassert : forall e,
      semantics (cassert e) (assert_cmd (pure_eval e)).

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

  Local Transparent ILPre_Ops.
  Local Transparent ILFun_Ops.

  Definition triple (P Q : sasn) (c : cmd) :=
    Forall sc : semCmd, (semantics c sc) ->> {{P}} sc {{Q}}.

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