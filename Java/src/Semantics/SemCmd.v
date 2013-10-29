Require Import Program SepAlg OpenILogic AssertionLogic SpecLogic SepAlgMap.
Require Import MapInterface MapFacts.
Require Import ILInsts ILogic ILEmbed Open Subst Stack Lang.

Import SepAlgNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Maximal Implicit Insertion.

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
  Inductive assume_sem (p : pure) : semCmdType :=
  | assume_ok : forall P s h, p s -> assume_sem p P 1 s h (Some (s, h)).
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

  Inductive assert_sem (p : pure) : semCmdType :=
  | assert_ok   : forall P s h (HP : p s),
    assert_sem p P 1 s h (Some (s, h))
  | assert_fail : forall P s h (HNP : ~p s),
    assert_sem p P 1 s h None.
  Program Definition assert_cmd p := @Build_semCmd (assert_sem p) _ _.
  Next Obligation.
    intros H; inversion H.
  Qed.
  Next Obligation.
    unfold frame_property; simpl; intros.
    inversion HSem; subst; eauto using assert_sem.
  Qed.

  (* |= {p}c{q} *)
  
  Program Definition sem_triple (p q : sasn) (c : semCmd) : spec :=
    mk_spec (fun P n => forall P' m k s h, Prog_wf_sub P P' -> m <= n -> k <= m -> 
                                           p s P' m h ->
      safe c P' k s h /\
      forall h' s', c P' k s h (Some (s', h')) -> (q s' P' (m - k) h')) _ _.
  Next Obligation.
    apply H0; try eassumption.
    etransitivity; eassumption.
  Qed.

End Commands.


  Local Transparent ILPre_Ops.
  Local Transparent ILFun_Ops.

  Add Parametric Morphism : sem_triple with signature
    lentails --> lentails ++> eq ==> lentails
    as sem_triple_entails_m.
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

  Add Parametric Morphism : sem_triple with signature
    lequiv ==> lequiv ==> eq ==> lequiv
    as sem_triple_lequiv_m.
  Proof.
    split.
    + rewrite H, H0; reflexivity.
    + rewrite <- H, <- H0; reflexivity.
  Qed.


Implicit Arguments Build_semCmd [].

Notation "{{ p }} c {{ q }}" := (sem_triple p q c) (at level 89,
  format "{{ p }} '/ '  c '/ '  {{ q }}").
