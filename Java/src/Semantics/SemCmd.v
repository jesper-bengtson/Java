Require Import SepAlg OpenILogic SepAlgMap.
Require Import MapInterface MapFacts.
Require Import ILInsts ILogic ILEmbed Open Subst Stack.
Require Import Program SpecLogic Heap ProtocolLogic Lang Traces.

Import SepAlgNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Maximal Implicit Insertion.

Section Commands.

  Definition semCmdType := Prog_wf -> PM -> nat -> stack -> heap -> traces -> option (stack * (heap * traces)) -> Prop.
  Definition safe (c : semCmdType) Pr PM n s h t := ~(c Pr PM n s h t None).
  Definition frame_property (c : semCmdType) :=
    forall Pr PM s s' (big big' frame h : heap) n t t'
      (HFrame : sa_mul h frame big)
      (HSafe  : forall m, m <= n -> safe c Pr PM m s h t)
      (HSem   : c Pr PM n s big t (Some (s', (big', t')))),
      exists h', sa_mul h' frame big' /\ c Pr PM n s h t (Some (s', (h', t'))).

  Record semCmd := {
    cmd_rel   :> Prog_wf -> PM -> nat -> stack -> heap -> traces -> option (stack * (heap * traces)) -> Prop;
    cmd_zero  :  forall Pr PM s h t cfg, ~(cmd_rel Pr PM 0 s h t cfg);
    cmd_frame :  frame_property cmd_rel
  }.

  Definition not_modifies (c : semCmdType) x : Prop :=
    forall Pr PM s s' h h' n t t' (HSem : c Pr PM n s h t (Some (s', (h', t')))),
      s x = s' x.

  Lemma safe_zero : forall (c : semCmd) Pr PM s h t, safe c Pr PM 0 s h t.
  Proof.
    intros; apply cmd_zero.
  Qed.
  
  Global Opaque sa_mul.

  Implicit Arguments Build_semCmd [].

  Program Definition later_cmd (c : semCmd) : semCmd := Build_semCmd
    (fun Pr PM n => match n return stack -> heap -> traces -> option (stack * (heap * traces)) -> Prop with
                  | O => fun _ _ _ _ => False
                  | S n => c Pr PM n end) _ _.
  Next Obligation.
    unfold frame_property; intros.
    destruct n as [| n]; unfold safe in HSafe; simpl in *; [contradiction |].
    eapply cmd_frame; eauto. 
    intros m HLe HFail; apply (HSafe (S m)); auto with arith.
  Qed.

  Inductive skip_sem : semCmdType :=
  | s_ok : forall Pr PM s h t, skip_sem Pr PM 1 s h t (Some (s, (h, t))).
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
  | seq_failL : forall Pr PM n s h t,
      c1 Pr PM n s h t None ->
      seq_sem c1 c2 Pr PM (S n) s h t None
  | seq_failR : forall Pr PM n n' s s' h h' t t',
      c1 Pr PM n s h t (Some (s', (h', t'))) ->
      c2 Pr PM n' s' h' t' None ->
      seq_sem c1 c2 Pr PM (S (n + n')) s h t None
  | seq_ok    : forall Pr PM n n0 s s0 s1 h h0 h1 t t0 t1,
      c1 Pr PM n  s  h  t  (Some (s0, (h0, t0))) ->
      c2 Pr PM n0 s0 h0 t0 (Some (s1, (h1, t1))) ->
      seq_sem c1 c2 Pr PM (S (n + n0)) s h t (Some (s1, (h1, t1))).
  Program Definition seq_cmd c1 c2 := @Build_semCmd (seq_sem c1 c2) _ _.
  Next Obligation.
    intros H; inversion H.
  Qed.
  Next Obligation with eauto using seq_sem.
    unfold frame_property; intros.
    inversion HSem; subst; clear HSem.
    edestruct (@cmd_frame c1) as [h0 [HFrame0 HSem0]]...
    + intros m HLe HFail; apply HSafe with (S m); [omega | ]... 
    + edestruct (@cmd_frame c2) with(n:=n1) as [hr [HFrame1 HSem1]]...
      intros m HLe HFail; apply HSafe with (S (n0 + m)); [omega | ]...
  Qed.

  (* Nondet *)
  Inductive nondet_sem (c1 c2 : semCmd) : semCmdType :=
  | nondet_failL : forall Pr PM n s h t,
      c1 Pr PM n s h t None ->
      nondet_sem c1 c2 Pr PM (S n) s h t None
  | nondet_okL   : forall Pr PM n s s' h h' t t',
      c1 Pr PM n s h t (Some (s', (h', t'))) ->
      nondet_sem c1 c2 Pr PM (S n) s h t (Some (s', (h', t')))
  | nondet_failR : forall Pr PM n s h t,
      c2 Pr PM n s h t None ->
      nondet_sem c1 c2 Pr PM (S n) s h t None
  | nondet_okR   : forall Pr PM n s s' h h' t t',
      c2 Pr PM n s h t (Some (s', (h', t'))) ->
      nondet_sem c1 c2 Pr PM (S n) s h t (Some (s', (h', t'))).
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
  | kleene_emp       : forall Pr PM s h t,
      kleene_sem c Pr PM 1 s h t (Some (s, (h, t)))
  | kleene_fail_one  : forall Pr PM n s h t,
      c Pr PM n s h t None ->
      kleene_sem c Pr PM (S n) s h t None
  | kleene_fail_many : forall Pr PM n n0 s s0 h h0 t t0,
      c Pr PM n s h t (Some (s0, (h0, t0))) ->
      kleene_sem c Pr PM n0 s0 h0 t0 None ->
      kleene_sem c Pr PM (S (n + n0)) s h t None
  | kleene_step_ok   : forall Pr PM n n0 s s0 s1 h h0 h1 t t0 t1,
      c Pr PM n s h t (Some (s0, (h0, t0))) ->
      kleene_sem c Pr PM n0 s0 h0 t0 (Some (s1, (h1, t1))) ->
      kleene_sem c Pr PM (S (n + n0)) s h t (Some (s1, (h1, t1))).
  Program Definition kleene_cmd c := @Build_semCmd (kleene_sem c) _ _.
  Next Obligation.
    intros H; inversion H.
  Qed.
  Next Obligation with eauto using kleene_sem.
    unfold frame_property; intros.
    generalize dependent h; remember (Some (s', (big', t'))) as cfg; induction HSem;
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
  Inductive assume_sem (p : vlogic) : semCmdType :=
  | assume_ok : forall Pr PM s h t, p s -> assume_sem p Pr PM 1 s h t (Some (s, (h, t))).
  Program Definition assume_cmd P := @Build_semCmd (assume_sem P) _ _.
  Next Obligation.
    intros H; inversion H.
  Qed.
  Next Obligation.
    unfold frame_property; simpl; intros.
    remember (Some (s', (big', t'))) as cfg; induction HSem.
    inversion Heqcfg; subst; eauto using assume_sem.
  Qed.

  Lemma assume_inv Pr PM e n s s0 h h0 t t0 (HSem : assume_cmd e Pr PM n s h t (Some (s0, (h0, t0)))) : 
      s = s0 /\ h = h0 /\ t = t0.
  Proof.  
    intros; remember (Some (s0, (h0, t0))); induction HSem; subst;
    try inversion Heqo; intuition.
  Qed.

  Inductive assert_sem (p : vlogic) : semCmdType :=
  | assert_ok   : forall Pr PM s h t (HP : p s),
    assert_sem p Pr PM 1 s h t (Some (s, (h, t)))
  | assert_fail : forall Pr PM s h t (HNP : ~p s),
    assert_sem p Pr PM 1 s h t None.
  Program Definition assert_cmd p := @Build_semCmd (assert_sem p) _ _.
  Next Obligation.
    intros H; inversion H.
  Qed.
  Next Obligation.
    unfold frame_property; simpl; intros.
    inversion HSem; subst; eauto using assert_sem.
  Qed.

  (* |= {p}c{q} *)
  Program Definition sem_triple (p q : psasn) (c : semCmd) : spec :=
    mk_spec (fun P n => forall P' PM m k s h t, Prog_wf_sub P P' -> m <= n -> k <= m -> 
                                           p PM s t P' m h ->
      (safe c P' PM k s h t) /\
      (forall t' h' s',  
      	c P' PM k s h t (Some (s', (h', t'))) ->
      		(q PM s' t' P' (m - k) h')
      		
      )
    ) _ _.
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
    intros p p' Hp q q' Hq c n x H P PM m k s h t HP Hmn Hkm Hp'.
    apply Hp in Hp'; try apply _.    
    simpl in *.
    specialize (H _ _ _ _ _ _ t HP Hmn Hkm Hp').
    destruct H as [Hsafe H].
    split; [assumption|].
    
    intros t' h' s' HC.
    apply Hq.
    specialize (H _ _ _ HC).
    apply H.
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
