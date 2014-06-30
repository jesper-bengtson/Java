Require Import SepAlg OpenILogic SepAlgMap.
Require Import MapInterface MapFacts.
Require Import ILInsts ILogic ILEmbed Open Subst Stack.
Require Import Program SpecLogic Heap ProtocolLogic Lang Traces ST.
Require Import AssertionLogic ST Util.

Import SepAlgNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Maximal Implicit Insertion.

Section Compatability.

  Fixpoint Comp (Pr : Prog_wf) (n : nat) (pr : STs) (tr : trace) (Q : nat -> STs -> Prop) : Prop :=
    match tr with 
      | t_end => Q n pr
      | t_send x v h tr' => match (find x pr) with
          | Some (st_send z P T) =>  P (stack_add z v (stack_empty _)) Pr n h /\ Comp Pr (n - 1) (add x (subst_ST z v T) pr) tr' Q
          | _ => False
        end
      | t_recv x v h tr' => match (find x pr) with
          | Some (st_recv z P T) =>  P (stack_add z v (stack_empty _)) Pr n h -> Comp Pr (n - 1) (add x (subst_ST z v T) pr) tr' Q
          | _ => False
        end
      | t_start x tr' tr'' => exists (T : ST), 
          Comp Pr (n-1) (add x T (empty _)) tr' (fun n' pr' => (forall c', In c' pr' -> MapsTo c' st_end pr') /\ 
          									 Comp Pr n' (add x (dual T) pr) tr'' Q)
      | t_tau tr' => Comp Pr (n - 1) pr tr' Q
    end.

  Lemma Comp_entails : forall Pr pr tr n (Q Q' : nat -> STs -> Prop), (forall m pr', Q m pr' -> Q' m pr') -> Comp Pr n pr tr Q -> Comp Pr n pr tr Q'.
  Proof with eauto.
    intros.
    generalize dependent pr. generalize dependent n. generalize dependent Q. generalize dependent Q'.
    induction tr; intros; simpl in *...
    - remember (find s pr); destruct o...
      destruct s0; try assumption; destruct H0...  
    - remember (find s pr); destruct o...
      destruct s0; try assumption... 
    - destruct H0 as [T ?]; exists T.
      eapply IHtr1; [| apply H0].
      intros. simpl in H1; destruct H1. split; [assumption |].
      eapply IHtr2. apply H. apply H2.
  Qed.

  Lemma Comp_split : forall Pr n pr tr (P Q : nat -> STs -> Prop), Comp Pr n pr tr P -> Comp Pr n pr tr Q -> Comp Pr n pr tr (fun n pr' => P n pr' /\ Q n pr').
  Proof with auto.
    intros.
    generalize dependent pr. generalize dependent n.
    induction tr; intros; simpl in *... 
    - remember (find s pr); destruct o...
      destruct s0; try assumption; destruct H, H0...
    - remember (find s pr); destruct o...
      destruct s0; try assumption...
    - (* create a witness that is the pointwise conjugation of T from H and T0 from H0 Ø)
       * So !z,P.T' + !z.P0.T0' becomes !z.{P /\ P0}.tail(T', T0') *)
      admit (* fangel, this needs a solution! *).
  Qed.

  Lemma Comp_partial : forall Pr n m k pr tr tr' (P Q : nat -> STs -> Prop), 
     n = trace_length tr ->
     n + m  <= k -> 
     Comp Pr k pr tr P -> 
     (forall pr, P m pr -> Comp Pr m pr tr' Q) -> 
     Comp Pr k pr (trace_append tr tr') Q.
  Proof with auto.
    admit.
Admitted.
  (*
    intros.
    generalize dependent pr. generalize dependent n.
    induction tr; intros; simpl in *; [subst | ..]...
    - remember (find s pr); destruct o...
      destruct s0; try assumption; destruct H0; split; [solve_model H0 |]. 
      assert (n - 1 = trace_length tr) by omega.
      specialize (IHtr _ H3); replace (n - 1 + m) with (n + m - 1) in * by omega...
    - remember (find s pr); destruct o...
      destruct s0; try assumption; intro.
      assert (n - 1 = trace_length tr) by omega. 
      specialize (IHtr _ H3); replace (n - 1 + m) with (n + m - 1) in * by omega...
    - destruct H0 as [T ?]; exists T. 
      eapply Comp_entails; [| apply H0].
      intros. simpl in H2; destruct H2.
      split; [assumption |].
      
      assert (m0 = trace_length tr2) by admit (* fangel, test *). 
      eapply IHtr2.
      specialize (IHtr2 _ H4); replace (n - 1 + m) with (n + m - 1) in * by omega..
    - assert (n - 1 = trace_length tr) by omega.
      specialize (IHtr _ H2); replace (n - 1 + m) with (n + m - 1) in * by omega...
  Qed. *)

End Compatability.

Section Commands.

  Definition semCmdType := Prog_wf -> nat -> stack -> heap -> NS.t -> trace -> option (stack * (heap * NS.t)) -> Prop.
  Definition safe (c : semCmdType) Pr n s h cl tr := forall tr' tr'' , tr = trace_append tr' tr'' -> ~(c Pr n s h cl tr' None).
  Definition frame_property (c : semCmdType) :=
    forall Pr s s' (big big' frame h : heap) cl cl' n tr
      (HFrame : @sa_mul heap HeapSepAlgOps h frame big) 
      (HSafe  : forall m, m <= n -> safe c Pr m s h cl tr)
      (HSem   : c Pr n s big cl tr (Some (s', (big', cl')))),
      exists h', sa_mul h' frame big' /\ c Pr n s h cl tr (Some (s', (h', cl'))).

  Record semCmd := {
    cmd_rel   :> Prog_wf -> nat -> stack -> heap -> NS.t -> trace -> option (stack * (heap * NS.t)) -> Prop;
    cmd_zero  :  forall Pr s h cl tr cfg, ~(cmd_rel Pr 0 s h cl tr cfg);
    cmd_frame :  frame_property cmd_rel
  }.

  Definition not_modifies (c : semCmdType) x : Prop :=
    forall Pr s s' h h' cl cl' n tr (HSem : c Pr n s h cl tr (Some (s', (h', cl')))),
      s x = s' x.

  Lemma safe_zero : forall (c : semCmd) Pr s h cl tr, safe c Pr 0 s h cl tr.
  Proof.
    unfold safe; intros; apply cmd_zero.
  Qed.
  
  Global Opaque sa_mul.

  Implicit Arguments Build_semCmd [].

  Program Definition later_cmd (c : semCmd) : semCmd := Build_semCmd
    (fun Pr n => match n return stack -> heap -> NS.t -> trace -> option (stack * (heap * NS.t) ) -> Prop with
                  | O => fun _ _ _ _ _ => False
                  | S n => c Pr n end) _ _.
  Next Obligation.
    unfold frame_property; intros.
    destruct n as [| n]; unfold safe in HSafe; simpl in *; [contradiction |].
    eapply cmd_frame; eauto. 
    intros m HLe HFail; apply (HSafe (S m)); auto with arith.
  Qed.

  Inductive skip_sem : semCmdType :=
  | s_ok : forall Pr s h cl, skip_sem Pr 1 s h cl (t_tau t_end) (Some (s, (h, cl))).
  Program Definition skip_cmd := @Build_semCmd skip_sem _ _.
  Next Obligation.
    intros H. inversion H.
  Qed.
  Next Obligation with auto using skip_sem.
    unfold frame_property; intros.
    inversion HSem; subst; clear HSem.
    exists h...
  Qed.

  (* Seq *)
  Inductive seq_sem (c1 c2 : semCmd) : semCmdType :=
  | seq_failL : forall Pr n s h cl tr,
      c1 Pr n s h cl tr None ->
      seq_sem c1 c2 Pr n s h cl tr None
  | seq_failR : forall Pr n n' s s' h h' tr tr' cl cl',
      c1 Pr n  s  h  cl  tr (Some (s', (h', cl'))) ->
      c2 Pr n' s' h' cl' tr' None ->
      seq_sem c1 c2 Pr (n + n') s h cl (trace_append tr tr') None
  | seq_ok    : forall Pr n n0 s s0 s1 h h0 h1 tr tr0 cl cl0 cl1,
      c1 Pr n  s  h  cl  tr  (Some (s0, (h0, cl0))) ->
      c2 Pr n0 s0 h0 cl0 tr0 (Some (s1, (h1, cl1))) ->
      seq_sem c1 c2 Pr (n + n0) s h cl (trace_append tr tr0) (Some (s1, (h1, cl1))).
  Program Definition seq_cmd c1 c2 := @Build_semCmd (seq_sem c1 c2) _ _.
  Next Obligation.
    intros H; inversion H; subst; [ apply cmd_zero in H0; assumption | ..];
    replace (n) with (0) in * by omega; apply cmd_zero in H1; assumption.
  Qed.
  Next Obligation with eauto using seq_sem.
    unfold frame_property; intros.
    inversion HSem; subst; clear HSem.
    edestruct (@cmd_frame c1) as [h0 [HFrame0 HSem0]]...
    + intros m HLe ? ? Htr HFail. 
      eapply HSafe with (m := m); [ omega | rewrite Htr; apply trace_appendC |]...
    + edestruct (@cmd_frame c2) with(n:=n1) as [hr [HFrame1 HSem1]]...
      intros m HLe ? ? Htr HFail.
      eapply HSafe with (m := n0 + m); [ omega | rewrite Htr; rewrite <- trace_appendC; reflexivity |]... 
  Qed.

  (* Nondet *)
  Inductive nondet_sem (c1 c2 : semCmd) : semCmdType :=
  | nondet_failL : forall Pr n s h tr cl,
      c1 Pr n s h cl tr None ->
      nondet_sem c1 c2 Pr n s h cl tr None
  | nondet_okL   : forall Pr n s s' h h' tr cl cl',
      c1 Pr n s h cl tr (Some (s', (h', cl'))) ->
      nondet_sem c1 c2 Pr n s h cl tr (Some (s', (h', cl')))
  | nondet_failR : forall Pr n s h tr cl,
      c2 Pr n s h cl tr None ->
      nondet_sem c1 c2 Pr n s h cl tr None
  | nondet_okR   : forall Pr n s s' h h' tr cl cl',
      c2 Pr n s h cl tr (Some (s', (h', cl'))) ->
      nondet_sem c1 c2 Pr n s h cl tr (Some (s', (h', cl'))).
  Program Definition nondet_cmd c1 c2 := @Build_semCmd (nondet_sem c1 c2) _ _.
  Next Obligation.
    intros H; inversion H; subst;
    apply cmd_zero in H0; assumption.
  Qed.
  Next Obligation with eauto using nondet_sem.
    unfold frame_property; intros.
    inversion HSem; subst; clear HSem.
    + edestruct (@cmd_frame c1) as [h0 [HFrame0 HSem0]]...
      intros m HLe ? ? Htr HFail; eapply HSafe with (m := m); [omega | ..]...
    + edestruct (@cmd_frame c2) as [h0 [HFrame0 HSem0]]...
      intros m HLe ? ? Htr HFail; eapply HSafe with (m := m); [omega | ..]...
  Qed.

  (* Kleene star *)
  Inductive kleene_sem (c : semCmd) : semCmdType :=
  | kleene_emp       : forall Pr s h cl,
      kleene_sem c Pr 1 s h cl t_end (Some (s, (h, cl)))
  | kleene_fail_one  : forall Pr n s h tr cl,
      c Pr n s h cl tr None ->
      kleene_sem c Pr n s h cl tr None
  | kleene_fail_many : forall Pr n n0 s s0 h h0 tr tr' cl cl0,
      c Pr n s h cl tr (Some (s0, (h0, cl0))) ->
      kleene_sem c Pr n0 s0 h0 cl0 tr' None ->
      kleene_sem c Pr (n + n0) s h cl (trace_append tr tr') None
  | kleene_step_ok   : forall Pr n n0 s s0 s1 h h0 h1 tr tr1 cl cl0 cl1,
      c Pr n s h cl tr (Some (s0, (h0, cl0))) ->
      kleene_sem c Pr n0 s0 h0 cl0 tr1 (Some (s1, (h1, cl1))) ->
      kleene_sem c Pr (n + n0) s h cl (trace_append tr tr1) (Some (s1, (h1, cl1))).
  Program Definition kleene_cmd c := @Build_semCmd (kleene_sem c) _ _.
  Next Obligation.
    intros H; inversion H; subst; [apply cmd_zero in H0; assumption | ..];
    replace (n) with (0) in * by omega; apply cmd_zero in H1; assumption.
  Qed.
  Next Obligation with eauto using kleene_sem.
    unfold frame_property; intros.
    generalize dependent h; remember (Some (s', (big', cl'))) as cfg; remember (tr) as tr'; generalize dependent tr; induction HSem; intros;
      inversion Heqcfg; subst; intros; clear Heqcfg...
    edestruct (@cmd_frame c) as [h' [HFrame0 HSem0]]...
    + intros m HLe ? ? Htr HFail; eapply HSafe with (m := m); [omega | rewrite Htr; apply trace_appendC |]...
    + destruct (IHHSem (eq_refl _) _ (eq_refl _) h' HFrame0) as [hr [HFrame1 HSem1]]...
      intros m HLe ? ? Htr HFail; eapply HSafe with (m := n + m); [omega | rewrite Htr; rewrite <- trace_appendC; reflexivity |]...
  Qed.

  (* TODO: update the description
     assume command -- this command is a bit of a hack that just skips if
     a check holds and loops otherwise, this way allowing to encode if/while
     using nondeterministic choice/Kleene star *)
  Inductive assume_sem (p : vlogic) : semCmdType :=
  | assume_ok : forall Pr s h cl, p s -> assume_sem p Pr 1 s h cl (t_tau t_end) (Some (s, (h, cl))).
  Program Definition assume_cmd P := @Build_semCmd (assume_sem P) _ _.
  Next Obligation.
    intros H; inversion H.
  Qed.
  Next Obligation with eauto using assume_sem.
    unfold frame_property; simpl; intros.
    remember (Some (s', (big', cl'))) as cfg; induction HSem.
    inversion Heqcfg; subst...
  Qed.

  Lemma assume_inv Pr e n s s0 h h0 cl cl0 tr (HSem : assume_cmd e Pr n s h cl tr (Some (s0, (h0, cl0)))) : 
      s = s0 /\ h = h0.
  Proof.  
    intros; remember (Some (s0, (h0, cl0))); induction HSem; subst;
    try inversion Heqo; intuition.
  Qed.

  Inductive assert_sem (p : vlogic) : semCmdType :=
  | assert_ok   : forall Pr s h cl (HP : p s),
    assert_sem p Pr 1 s h cl (t_tau t_end) (Some (s, (h, cl)))
  | assert_fail : forall Pr s h cl (HNP : ~p s),
    assert_sem p Pr 1 s h cl (t_tau t_end) None.
  Program Definition assert_cmd p := @Build_semCmd (assert_sem p) _ _.
  Next Obligation.
    intros H; inversion H.
  Qed.
  Next Obligation with eauto using assert_sem.
    unfold frame_property; simpl; intros.
    inversion HSem; subst...
  Qed.


  (* |= {p}c{q} *)
  Program Definition sem_triple (p q : psasn) (c : semCmd) : spec :=
    mk_spec (fun P n => forall P' m k s h cl STs, Prog_wf_sub P P' -> m <= n -> k <= m -> 
                                           p s STs P' m h ->
      (forall tr cfg, c P' k s h cl tr cfg -> Comp P' m STs tr (fun n pr => cfg <> None)) /\
      (forall tr h' s' cl',  
      	c P' k s h cl tr (Some (s', (h', cl'))) ->
      		Comp P' m STs tr (fun n pr => (q s' pr P' n h'))
      		
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
    intros p p' Hp q q' Hq c n x H P m k s h cl pr HP Hmn Hkm Hp'.
    apply Hp in Hp'; try apply _.    
    simpl in *.
    specialize (H _ _ _ _ _ cl pr HP Hmn Hkm Hp').
    destruct H as [Hsafe H].
    split; [assumption|].
    
    intros tr h' s' cl' HC.
    eapply Comp_entails; [intros; apply Hq; apply H0 |].
    specialize (H _ _ _ _ HC).
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
