Require Import Program SepAlg SepAlgInsts AssertionLogic SpecLogic SepAlgMap.
Require Import MapInterface MapFacts Omega.

Require Import Charge.Logics.ILInsts.
Require Import Charge.Logics.ILogic.
Require Import Charge.Logics.ILEmbed.
Require Import Charge.Logics.BILogic.
Require Import Charge.Open.OpenILogic. 
Require Import Charge.Open.Open.
Require Import Charge.Open.Subst.
Require Import Charge.Open.Stack.

Require Import Java.Language.Lang.
Require Import Java.Semantics.SemCmd.
Require Import Java.Semantics.SemCmdRules.
Require Import Java.Logic.HeapArr.

Import SepAlgNotations.

Set Implicit Arguments.
Unset Strict Implicit.

Section Commands.

  Inductive assign_sem (x : Lang.var) (e : dexpr) : semCmdType :=
  | assign_ok : forall P s h v
                       (He: eval e s = v),
      assign_sem x e P 1 s h (Some (stack_add x v s, h)).
  Program Definition assign_cmd x e := Build_semCmd (assign_sem x e) _ _.
  Next Obligation.
    intros H; inversion H.
  Qed.
  Next Obligation with eauto using assign_sem.
    unfold frame_property; intros.
    inversion HSem; subst; clear HSem; exists h...
  Qed.

  Inductive read_sem (x y : Lang.var) (f : field) : semCmdType :=
  | read_ok : forall ref v P (s : stack) (h : heap)
      (Rref  : s y = vptr ref)
      (Rmaps : MapsTo (ref,f) v (fst h)),
      read_sem x y f P 1 s h (Some (stack_add x v s, h))
  | read_fail : forall ref P s (h : heap_ptr) (h' : heap_arr)
      (Sref   : s y = vptr ref)
      (Snotin : ~ In (ref,f) h),
      read_sem x y f P 1 s (h, h') None.
  Program Definition read_cmd x y f := Build_semCmd (read_sem x y f) _ _.
  Next Obligation.
    intros H; inversion H.
  Qed.
  Next Obligation with eauto using read_sem.
    unfold frame_property; intros.
    inversion HSem; subst n s0 h0 s' big'; clear HSem; exists h; intuition.
    apply read_ok with ref; [assumption |]; specialize (HSafe _ (le_n _)).
    destruct h, big, frame; simpl in *; subst.
    apply sa_mul_split in HFrame.
    destruct HFrame as [HFrame _].
    destruct (sa_mul_mapstoR HFrame Rmaps) as [[H1 H2] | [H1 H2]]; [assumption|].
    contradiction HSafe; apply read_fail with ref; assumption.
  Qed.

Require Import Compare_dec.

  Lemma in_list_fresh (lst : list nat) :
    exists n, ~ List.In n lst.
  Proof.
    assert (exists n, forall x, List.In x lst -> n > x). {
      induction lst. 
      + exists 0; intros x H. destruct H.
      + destruct IHlst as [n IHlst].
        destruct (gt_dec n a).
        * exists n; intros. simpl in H.
          destruct H. subst. assumption.
          apply IHlst. apply H.
        * assert (n <= a) by omega; clear n0.          
          exists (S a); intros. simpl in H0.
          destruct H0. subst. omega.
          specialize (IHlst x H0). omega.
    }
    destruct H as [n H].                                                         
    exists n. intros Hn. 
    specialize (H n Hn). omega.
  Qed.

  Lemma heap_arr_exists_fresh (h : heap_arr) :
    exists k, forall i, ~ In (k, i) h.
  Proof.
    assert (forall lst, exists k, forall i, ~ In (k, i) h /\ ~List.In k lst).
    generalize dependent h.
    apply (@map_induction (arrptr * nat) _ _ _ val 
                          (fun (h : heap_arr) => forall lst, exists k : arrptr, 
                                                   forall i : nat, ~ In (k, i) h /\ 
                                                                   ~ List.In k lst)).
    + intros.
      destruct (in_list_fresh lst) as [x H1].
      exists x; intros. split; [|assumption].
      intros H2.
      rewrite elements_Empty in H.
      rewrite elements_in_iff in H2.
      destruct H2 as [e H2]; rewrite H in H2.
      inversion H2.
    + intros. destruct x; simpl in *.
      specialize (H (a::lst)).
      destruct H as [k H].
      exists k; intros.
      specialize (H i). destruct H as [H2 H3].
      simpl in H3.
      assert (a <> k /\ ~ List.In k lst). {
        split. intros H4. apply H3. left. assumption.
        intros H. apply H3. right. apply H.
      }
      destruct H as [H4 H5].
      split; [|assumption].
      unfold Add in H1.
      specialize (H1 (k, i)).
      rewrite add_neq_o in H1.
      intros H. apply H2.
      rewrite in_find_iff; rewrite in_find_iff in H.
      intros H6.
      apply H. rewrite H1. apply H6.
      unfold Equivalence.equiv, complement; simpl.
      intros. inversion H; subst. apply H4. reflexivity.
    + destruct (H nil) as [k H1]; clear H.
      exists k; intros. destruct (H1 i) as [H _].
      apply H.
  Qed.


(*
  Require Import ZArith.
  Definition valid_path (vpath : list val) := 
    List.Forall (fun v => exists a, v = vint a /\ (a >= 0)%Z) vpath.
*)
  Inductive read_arr_sem (x y : Lang.var) (path : list dexpr) : semCmdType :=
  | read_arr_ok P arr s hp ha v vpath
                (Sref : s y = varr arr)
                (Smap : List.map (fun e => eval e s) path = vpath)
(*                (Sarr : valid_path vpath)*)
                (Sfind : find_heap_arr arr (List.map val_to_nat vpath) ha = Some v) :
      read_arr_sem x y path P 1 s (hp, ha) (Some (stack_add x v s, (hp, ha)))
  | read_arr_fail P arr s h vpath
                  (Sref : s y = varr arr)
                  (Smap : List.map (fun e => eval e s) path = vpath)
                  (Sarr : ~ in_heap_arr arr (List.map val_to_nat vpath) (snd h)) :
      read_arr_sem x y path P 1 s h None.
  Program Definition read_arr_cmd x y path := Build_semCmd (read_arr_sem x y path) _ _.
  Next Obligation.
    intros H. inversion H.
  Qed.
  Next Obligation.
    unfold frame_property; intros; exists h.
    inversion HSem; subst; specialize (HSafe _ (le_n _)). 
    split; [assumption|].
    destruct h as [hp' ha'].
    apply read_arr_ok with (arr := arr) (vpath := (List.map (fun e : dexpr => eval e s)) path);
      try assumption; try reflexivity.
    destruct frame.
    apply sa_mul_split in HFrame as [_ HFrame].

    assert (in_heap_arr arr (List.map val_to_nat (List.map (fun e : dexpr => eval e s) path)) ha').
    apply dec_double_neg; [apply in_heap_arr_dec | intro H].
    apply HSafe.
    eapply read_arr_fail; try eassumption; try reflexivity.
    eapply find_heap_arr_frame; eauto.
  Qed.    

  Inductive write_arr_sem (x : Lang.var) (path : list dexpr) (e : dexpr) : semCmdType :=
  | write_arr_ok P arr s hp ha ha' vpath
                 (Sref : s x = varr arr)
                 (Smap : List.map (fun e' => eval e' s) path = vpath)
                 (Sin  : in_heap_arr arr (List.map val_to_nat vpath) ha)
                 (Sha  : add_heap_arr arr (List.map val_to_nat vpath) ha (eval e s) = Some ha') :
      write_arr_sem x path e P 1 s (hp, ha) (Some (s, (hp, ha')))
  | write_arr_fail P arr s h vpath
                   (Sref : s x = varr arr)
                   (Smap : List.map (fun e' => eval e' s) path = vpath)
                   (Sin  : ~ in_heap_arr arr (List.map val_to_nat vpath) (snd h)) :
      write_arr_sem x path e P 1 s h None.
  Program Definition write_arr_cmd x path e := Build_semCmd (write_arr_sem x path e) _ _.
  Next Obligation.
    intros H. inversion H.
  Qed.
  Next Obligation.
    unfold frame_property; intros; inversion HSem; subst; clear HSem.
    destruct h, frame.
    apply sa_mul_split in HFrame as [Hhp Hha].
    specialize (HSafe _ (le_n _)).
    assert (in_heap_arr arr
          (List.map val_to_nat (List.map (fun e' : dexpr => eval e' s') path))
          h0). {
      apply dec_double_neg; [apply in_heap_arr_dec | intro H].
      apply HSafe; eapply write_arr_fail; try eassumption; reflexivity.
    }

    destruct (add_heap_arr_frame _ _ _ _ _ _ _ Hha Sha H) as [ha'' [H1 H2]].
    exists (h, ha'').
    split.
    split; simpl. apply Hhp. apply H1.
    eapply write_arr_ok; try eassumption; reflexivity.
  Qed.

  Inductive alloc_arr_sem (x : Lang.var) (e : dexpr) : semCmdType :=
  | alloc_arr_ok (P : Program) (s s' : stack) (hp : heap_ptr) (ha ha' : heap_arr) (n : nat)
                 (Sfresh_ha : forall i, ~ In (n, i) ha) 
                 (Sha : alloc_heap_arr n (val_to_nat (eval e s)) ha === ha') 
                 (Ss : s' = stack_add x (varr n) s) :
      alloc_arr_sem x e P 1 s (hp, ha) (Some (s', (hp, ha'))).
  Program Definition alloc_arr_cmd x e := Build_semCmd (alloc_arr_sem x e) _ _.
  Next Obligation.
    intros H; inversion H.
  Qed.
  Next Obligation.
    admit.
    (*
    unfold frame_property; intros; inversion HSem; subst P n s s' big big'.
    destruct h, frame.
    apply sa_mul_split in HFrame as [Hhp Hha].
    specialize (HSafe _ (le_n _)).
    Lemma alloc_heap_arr_frame (n m : nat) (h frame h' h'' : heap_arr)
          (Hfresh : forall i, ~ In (n, i) frame)
          (Hh : alloc_heap_arr n m h === h')
          (HFrame : sa_mul h'' frame h) :
      exists h''', alloc_heap_arr n m h'' === h''' /\ sa_mul h''' frame h'.
    Proof.
      admit.
      (*
      generalize dependent h'; induction m; simpl in *; intros.
      + setoid_rewrite <- Hh.
        exists (add (n, 0) null h''); split; [reflexivity|].
        apply sa_mul_add; [assumption | apply Hfresh]. 
      + assert (alloc_heap_arr n m h === alloc_heap_arr n m h) by reflexivity.
        destruct (IHm _ H) as [h'''' [H1 H2]].
        exists (add (n, m) null h'''').
        split.
        rewrite H1. reflexivity.
        rewrite <- Hh.
        apply sa_mul_add. assumption.
        apply Hfresh.
*)
    Admitted.
    admit.
    
    assert (forall i : nat, ~ In (n0, i) h2) as Sfresh_frame. {
      intros i H; apply Sfresh_ha with i.
      apply sa_mulC in Hha; destruct (sa_mul_inL Hha H); assumption.
    }
    destruct (alloc_heap_arr_frame Sfresh_frame Sha Hha) as [ha'' [H1 H2]].
    exists (h, ha''). split. split; simpl; assumption.
    apply alloc_arr_ok with n0; try assumption.
    intros i H.
    specialize (Sfresh_ha i). apply Sfresh_ha.
    destruct (sa_mul_inL Hha H). apply H3.
*)
  Admitted.

  Inductive alloc_sem (x : Lang.var) (C : class) : semCmdType :=
  | alloc_ok : forall (P : Program) (s s0 : stack) (h h0 : heap_ptr) (h' : heap_arr) n fields
      (Snotnull : (n, C) <> pnull)
      (Sfresh_h : forall f, ~ In ((n, C), f) h)
      (Sfields  : field_lookup P C fields)
      (Sh0      : sa_mul h
        (fold_right (fun f h' => add ((n, C), f) (pnull : val) h') heap_ptr_unit fields) h0)
      (Ss0      : s0 = stack_add x (vptr (n, C)) s),
      alloc_sem x C P 1 s (h, h') (Some (s0, (h0, h'))).
  Program Definition alloc_cmd x C := Build_semCmd (alloc_sem x C) _ _.
  Next Obligation.
    intros H; inversion H.
  Qed.
  Next Obligation.
    unfold frame_property; intros.
    inversion HSem; subst; clear HSem.
    destruct h, frame; simpl in *.
    apply sa_mul_split in HFrame. destruct HFrame as [HFrame HFrameArr].
    destruct (sa_mulA HFrame Sh0) as [h5 [H1 H2]].
    apply sa_mulC in H2; destruct (sa_mulA H1 H2) as [h6 [H3 H5]].
    exists (h6, h2).
    split; [split; simpl; [apply sa_mulC|]; assumption|].
    eapply alloc_ok; [eassumption | | eassumption | apply sa_mulC; assumption | reflexivity].
    intros f H6; apply (Sfresh_h f).
    apply sa_mulC in H2.
    destruct (sa_mul_inL H2 H6) as [H8 H9].    
    destruct (sa_mul_inR Sh0 H9) as [[H10 H11] | [H10 H11]]; [assumption|].
    apply sa_mulC in H1; destruct (sa_mul_inL H1 H10); intuition.
  Qed.

  Inductive write_sem (x:Lang.var) (f:field) (e:dexpr) : semCmdType := 
  | write_ok : forall P (s: stack) (h h' : heap_ptr) (h'' : heap_arr) ref v
      (Sref: s x = vptr ref)
      (Sin:  In (ref,f) h )
      (Heval : eval e s = v)
      (Sadd: h' = add (ref,f) v h ),
      write_sem x f e P 1 s (h, h'') (Some (s, (h', h'')))
  | write_fail : forall P (s: stack) h h'' ref
      (Sref:   s x = vptr ref)
      (Sin : ~ In (ref, f) h),
      write_sem x f e P 1 s (h, h'') None.
  Program Definition write_cmd x f e := Build_semCmd (write_sem x f e) _ _.
  Next Obligation.
    intros H; inversion H.
  Qed.
  Next Obligation.
    unfold frame_property; intros.
    inversion HSem. subst; clear HSem.
    destruct h, frame; simpl in *.
    apply sa_mul_split in HFrame as [HFrame HFramePtr].
    assert (~ In (ref, f) h2).
    intros H. 
    apply (HSafe 1); [omega |].
    eapply write_fail; [eassumption|].
    destruct (sa_mul_inR HFrame Sin); intuition.
    exists ((add (ref, f) (eval e s') h, h1)). split.
    split.
    apply sa_mul_add; assumption. simpl. assumption.
    eapply write_ok; try eassumption; try reflexivity.
    destruct (sa_mul_inR HFrame Sin); intuition.
  Qed.

  Fixpoint create_stack (ps : list Lang.var) (vs : list val) : stack :=
    match ps, vs with
      | nil, nil => stack_empty Lang.var val
      | p :: ps, v :: vs =>
        stack_add p v (create_stack ps vs)
      | _, _ => stack_empty Lang.var val
    end.
        
  Inductive call_sem (rvar : Lang.var) (C : open class) m es (c : cmd) (sc : semCmd)
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
  | semdcall  : forall (x y : Lang.var) m es c sc 
      (HSem     : semantics c sc),
      semantics (cdcall x y m es) 
        (call_cmd x ((fun e s => val_class (e s)) (var_expr y)) m ((E_var y) :: es) c sc)
  | semscall  : forall (x : Lang.var) (C : class) m es c sc
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

  Definition method_spec C m (ps : list Lang.var) (rn : Lang.var) (P Q : sasn) := (
    NoDup (rn :: ps) /\\
    Exists ps' : (list Lang.var), Exists c : cmd, Exists re : dexpr,
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
    admit.
    (*
    intros C m ps rn P P' HP Q Q' HQ. unfold method_spec.
    (* Unravel the two almost identical sides of the entailment first because
        setoid_rewrite doesn't seem to go under these binders. *)
    apply lpropandL; intro H. apply lpropandR; [assumption|].
    lexistsL ps' c re. lexistsR ps' c re.
    apply landR; [apply landL1; reflexivity | apply landL2].
    admit.
(*    setoid_rewrite HP. setoid_rewrite HQ. reflexivity.*)
*)
  Admitted.

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
    unfold triple. apply lforallR; intro sc. apply lpropimplR; intros Hsc.
    apply lforallL with sc. apply lpropimplL; [assumption|]. apply rule_of_consequence; assumption.
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
  
  Lemma rule_frame_ax_list P Q R c (xs: list Lang.var)
    (HMod : forall x, ~ List.In x xs -> c_not_modifies c x) :
    {[ P ]} c {[ Q ]} |--
    {[ P ** R ]} c {[ Q ** Exists vs, apply_subst R (subst_fresh vs xs) ]}.
  Proof.
    unfold triple. apply lforallR; intro sc; apply lpropimplR; intro Hsc. apply lforallL with sc. 
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
    + apply lforallR; intro sc. apply lpropimplR; intro Hsc; apply lforallR; intro x.
      apply lforallL with x; apply lforallL with sc. apply lpropimplL; [assumption | reflexivity].
    + apply lforallR; intro x; apply lforallR; intro sc. apply lpropimplR; intro Hsc.
      apply lforallL with sc. apply lpropimplL; [assumption | apply lforallL with x; reflexivity].
  Qed.
  
  Lemma existentialise_triple (x : Lang.var) (P Q : sasn) c (G : spec) 
	(H : forall (v : val), G |-- {[@lembedand vlogic sasn _ _ (open_eq (x/V) (`v)) P]} c {[Q]}) :
    G |-- {[P]} c {[Q]}.
  Proof.
    eapply roc_pre; [apply existentialise_var with (x0 := x)|].
    rewrite <- exists_into_precond2. apply lforallR; intro y. apply H.
  Qed.

End StructuralRules.