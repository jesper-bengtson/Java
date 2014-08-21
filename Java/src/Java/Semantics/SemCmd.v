Require Import SepAlg OpenILogic Charge.SepAlg.SepAlgMap. 
Require Import MapInterface MapFacts.
Require Import ILInsts ILogic ILEmbed Open Subst Stack.
Require Import Program Java.Logic.SpecLogic Heap ProtocolLogic Lang Traces Java.Logic.ST.
Require Import AssertionLogic ST Util.

Import SepAlgNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Maximal Implicit Insertion.

Section Compatability.

  Program Fixpoint Comp (Pr : Prog_wf) (n : nat) (pr : STs) (tr : trace) (Q : psasn) : Prop :=
    match tr with 
      | t_end s h _ => Q s pr Pr (n - 1) h
      | t_fail => False
      | t_send x v h tr' => match (find x pr) with
          | Some (st_send z P T) =>  P (stack_add z v (stack_empty _)) Pr n h /\ Comp Pr (n - 1) (add x (subst_ST z v T) pr) tr' Q
          | _ => False
        end
      | t_recv x tr' => match (find x pr) with
          | Some (st_recv z P T) =>  forall v h, P (stack_add z (vptr v) (stack_empty _)) Pr n h ->
                                                 Comp Pr (n - 1) (add x (subst_ST z v T) pr) (tr' v h) Q
          | _ => False
        end
      | t_start x tr' tr'' => exists (T : ST), 
          Comp Pr (n-1) (add x T (empty _)) tr' 
               (fun s => mk_pasn (fun pr' Pr n _ => (forall c', In c' pr' -> MapsTo c' st_end pr') /\ 
          			                               forall m, m <= n -> forall Pr', Prog_wf_sub Pr Pr' ->
          			                                  Comp Pr' m (add x (dual T) pr) tr'' Q) _ _ _ _)
      | t_tau _ _ _ tr' => Comp Pr (n - 1) pr tr' Q
    end.
    Next Obligation.
	  split; [|assumption].
	  intros. rewrite <- H. apply H0.
	  rewrite H. assumption.
	Defined.
    Next Obligation.
	  split. assumption. intros. eapply H1.
	  assumption. transitivity P'; assumption.
	Defined.

  Local Transparent ILPre_Ops.
  Local Transparent ILFun_Ops.

  Lemma Comp_entails Pr pr tr n (Q Q' : psasn) (HQQ' : Q |-- Q') (H : Comp Pr n pr tr Q) : 
  	Comp Pr n pr tr Q'.
  Proof with eauto.
    intros.
    generalize dependent pr. generalize dependent n. generalize dependent Pr. generalize dependent Q. generalize dependent Q'.
    induction tr; intros; simpl in *...
    - remember (find s pr); destruct o...
      destruct s0; try assumption; destruct H...  
    - remember (find s pr); destruct o...
      destruct s0; try assumption... 
    - destruct H as [T ?]; exists T.
      eapply IHtr1; [| apply H].
      intros. simpl in *. destruct H0; split; [assumption|].
      intros; eapply IHtr2. eapply HQQ'. apply H1. assumption. assumption.
  Qed.
(*
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
*)
End Compatability.

Section Commands.

  Definition semCmdType := Prog_wf -> stack -> heap -> NS.t -> trace -> Prop.
  Definition safe (c : semCmdType) Pr s h cl := forall tr, c Pr s h cl tr -> trace_safe tr.

  Inductive frame_trace (frame : heap) : trace -> trace -> Prop :=
  	| ft_end s big cl h : sa_mul h frame big -> frame_trace frame (t_end s h cl) (t_end s big cl)
  	| ft_fail tr : frame_trace frame t_fail tr
  	| ft_tau tr tr' s big cl h : frame_trace frame tr tr' ->
  	                 sa_mul h frame big -> frame_trace frame (t_tau s h cl tr) (t_tau s big cl tr')
  	| ft_send tr tr' x v h big : frame_trace frame tr tr' ->
  	                            sa_mul h frame big -> frame_trace frame (t_send x v h tr) (t_send x v big tr')
  	| ft_recv f g c : (forall x h, frame_trace frame (f x h) (g x h)) -> frame_trace frame (t_recv c f) (t_recv c g)
  	| ft_start c tr tr' tr'' : frame_trace frame tr tr' -> frame_trace frame (t_start c tr'' tr) (t_start c tr'' tr').

  Definition frame_property (c : semCmdType) : Prop :=
    forall Pr s (big frame h : heap) cl tr
      (HFrame : @sa_mul heap HeapSepAlgOps h frame big) 
      (HSafe : safe c Pr s h cl)
      (HSem   : c Pr s big cl tr),
      exists tr', frame_trace frame tr' tr /\ c Pr s h cl tr'.
(*
  Definition frame_property (c : semCmdType) :=
    forall Pr s s' (big big' frame h : heap) cl cl' tr
      (HFrame : @sa_mul heap HeapSepAlgOps h frame big) 
      (HSafe  : safe c Pr m s h cl tr)
      (HSem   : c Pr s big cl tr(* (Some (s', (big', cl'))))*),
      exists h', sa_mul h' frame big' /\ c Pr n s h cl tr (Some (s', (h', cl'))).
*)
  Record semCmd := {
    cmd_rel   :> Prog_wf -> stack -> heap -> NS.t -> trace -> Prop;
    cmd_frame : frame_property cmd_rel
  }.
  Print semCmd.
(*
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
*)

  Inductive skip_sem : semCmdType :=
  | s_ok : forall Pr s h cl, skip_sem Pr s h cl (t_end s h cl).
  Program Definition skip_cmd := @Build_semCmd skip_sem _.
(*  Next Obligation.
    intros H. inversion H.
  Qed.*)
  Next Obligation.
	unfold frame_property.
	intros. inversion HSem; subst.
	exists (t_end s h cl).
	split; constructor; assumption.
  Qed.

  (* Seq *)
 
  Inductive trace_append_cmd (Pr : Prog_wf) (c : semCmd) : trace -> trace -> Prop :=
    | ta_fail : trace_append_cmd Pr c t_fail t_fail
  	| ta_send p v h tr tr' : trace_append_cmd Pr c tr tr' ->
  	                         trace_append_cmd Pr c (t_send p v h tr) (t_send p v h tr')
  	| ta_recv p f g: (forall v h, trace_append_cmd Pr c (f v h) (g v h)) ->
  	                              trace_append_cmd Pr c (t_recv p f) (t_recv p g)
  	| ta_end s h tr cl : c Pr s h cl tr -> trace_append_cmd Pr c (t_end s h cl) (t_tau s h cl tr)
  	| ta_tau s h tr tr' cl : trace_append_cmd Pr c tr tr' -> 
  	                         trace_append_cmd Pr c (t_tau s h cl tr) (t_tau s h cl tr')
    | ta_start p tr tr' tr'' : trace_append_cmd Pr c tr' tr'' -> 
                               trace_append_cmd Pr c (t_start p tr tr') (t_start p tr tr'').                
    
 
    Lemma trace_append_cmd_frame_trace Pr c tr tr' tr'' frame
    	(Hc : trace_append_cmd Pr c tr tr') (HFrame : frame_trace frame tr'' tr) :
    	exists tr''', trace_append_cmd Pr c tr'' tr''' /\ frame_trace frame tr''' tr'.
    Proof with eauto.
 	  admit.
 	  (*
      generalize dependent tr'. induction HFrame; intros.
      + inversion Hc.
      + exists t_fail; try repeat constructor.
      + inversion Hc; subst.
        inversion HFrame; subst.
        inversion Hc; subst; [|inversion H1].
        admit. inversion H1.
        edestruct (@cmd_frame c) as [tr2 [HFrame2 HSem2]]...
        inversion Hc.
        exists (t_tau s h cl tr2).
        split.
        constructor; assumption.
        constructor; assumption.
        exists (t_tau s h cl t_fail). split; try repeat constructor. assumption.
        specialize (IHHFrame _ H5).
        destruct IHHFrame as [tr''' [H1 H2]].
        exists (t_tau s h cl tr'''). 
        split; constructor; assumption.
      + inversion Hc; subst.
        specialize (IHHFrame _ H5).
        destruct IHHFrame as [tr''' [H1 H2]].
        exists (t_send x v h tr''').
        split; constructor; assumption.
      + inversion Hc; subst.
     assert (forall x h, 
     exists tr''' : trace,
       trace_append_cmd Pr c (f x h) tr''' /\ frame_trace frame tr''' (g0 x h)).
       intros. apply H0. apply H4. clear H0.
       
       Require Import ChoiceFacts.
       Axiom AC_fun : FunctionalChoice.
       assert (forall (x : ptr), exists tr''' : heap -> trace, forall h : heap,
       trace_append_cmd Pr c (f x h) (tr''' h) /\
       frame_trace frame (tr''' h) (g0 x h)).
       intros. specialize (H1 x). apply AC_fun in H1.
       apply H1. clear H1.
       apply AC_fun in H0. destruct H0.
       exists (t_recv c0 x). 
       split; constructor; intros; firstorder.
      + inversion Hc.
*)
   Qed.


    Inductive seq_sem (c1 c2 : semCmd) : semCmdType :=
    | seq_ok : forall Pr s h cl tr tr',
    	c1 Pr s h cl tr ->
     	trace_append_cmd Pr c2 tr tr' ->
    	seq_sem c1 c2 Pr s h cl tr'.
  Program Definition seq_cmd c1 c2 := @Build_semCmd (seq_sem c1 c2) _.
(*  Next Obligation.
	intros H; inversion H; subst. inversion H1.
  Qed.*)
  Next Obligation with eauto using seq_sem.
    unfold frame_property; intros.
    inversion HSem; subst.
    edestruct (@cmd_frame c1) as [tr1 [HFrame1 Hsem1]]... 
    intros tr' Hc.
    + intros tr' Hc. 
      clear -HSafe Hc.
      destruct tr'; simpl in *; try apply I.
      - specialize (HSafe t_fail). apply HSafe. 
        eapply seq_ok; [eassumption|]. constructor.
      - unfold safe in HSafe. 
	    assert (exists tr'', trace_append_cmd Pr c2 tr' tr'') by admit.
	    destruct H as [tr'' H].
	    specialize (HSafe (t_send s0 v h0 tr'')).
	    simpl in HSafe. 
	    assert (trace_append_cmd Pr c2 (t_send s0 v h0 tr') (t_send s0 v h0 tr'')).
	    constructor. assumption.
	    pose proof (seq_ok Hc H0).
	    specialize (HSafe H1).
	    
	    apply HSafe.
      unfold safe in HSafe.
      
      specialize (H0 Htrace).
    apply HSafe.
    eapply seq_ok. eassumption.
    pose proof (trace_append_cmd_frame_trace H0 HFrame1).
    destruct H1 as [tr' [H1 H2]].
    exists tr'. split; [assumption|].
    eapply seq_ok; eassumption.
  Qed.

  (* Nondet *)
  Inductive nondet_sem (c1 c2 : semCmd) : semCmdType :=
  | nondetL   : forall Pr s h cl tr,
      c1 Pr s h cl tr ->
      (nondet_sem c1 c2) Pr s h cl tr
   | nondetR   : forall Pr s h tr cl,
      c2 Pr s h cl tr ->
      nondet_sem c1 c2 Pr s h cl tr.
  Program Definition nondet_cmd c1 c2 := @Build_semCmd (nondet_sem c1 c2) _.
(*  Next Obligation.
    intros H; inversion H; subst;
    apply cmd_zero in H0; assumption.
  Qed.*)
  Next Obligation with eauto using nondet_sem.
	intros Pr s big frame h cl tr HFrame HSem.
	inversion HSem; subst.
	+ edestruct (@cmd_frame c1)...
	  exists x. destruct H0 as [H1 H2]. split; [assumption|].
	  apply nondetL; assumption.
	+ edestruct (@cmd_frame c2)...
	  exists x; destruct H0 as [H1 H2]; split; [assumption|].
	  apply nondetR; assumption.
  Qed.

  (* Kleene star *)

  Inductive kleene_sem (c : semCmd) : semCmdType :=
  | kleene_emp       : forall Pr s h cl,
      kleene_sem c Pr s h cl (t_end s h cl)
  | kleene_step_ok   : forall Pr s h tr tr1 cl,
      c Pr s h cl tr ->
      trace_append_cmd Pr c tr tr1 ->
      kleene_sem c Pr s h cl tr1.
  Program Definition kleene_cmd c := @Build_semCmd (kleene_sem c) _.
(*  Next Obligation.
	intros H; inversion H; subst. inversion H1. 
  Qed.*)
  Next Obligation with eauto using kleene_sem.
    unfold frame_property; intros.
    generalize dependent h. induction HSem; intros.
    + exists (t_end s h0 cl).
      split; try repeat constructor; assumption.
    + edestruct (@cmd_frame c) as [tr2 [HFrame1 Hsem1]]...            
      pose proof (trace_append_cmd_frame_trace H0 HFrame1).
      destruct H1 as [tr' [H1 H2]].
      exists tr'. split; [assumption|].
      eapply kleene_step_ok; eassumption.
  Qed.

  (* TODO: update the description
     assume command -- this command is a bit of a hack that just skips if
     a check holds and loops otherwise, this way allowing to encode if/while
     using nondeterministic choice/Kleene star *)
  Inductive assume_sem (p : vlogic) : semCmdType :=
  | assume_ok : forall Pr s h cl, p s -> assume_sem p Pr s h cl (t_end s h cl).
  Program Definition assume_cmd P := @Build_semCmd (assume_sem P) _.
(*  Next Obligation.
    intros H; inversion H.
  Qed.*)
  Next Obligation.
    unfold frame_property; intros.
    induction HSem.
    exists (t_end s h cl).
    split; try repeat constructor; assumption.
  Qed.

(*
  Lemma assume_inv Pr e n s s0 h h0 cl cl0 tr (HSem : assume_cmd e Pr n s h cl tr (Some (s0, (h0, cl0)))) : 
      s = s0 /\ h = h0.
  Proof.  
    intros; remember (Some (s0, (h0, cl0))); induction HSem; subst;
    try inversion Heqo; intuition.
  Qed.
*)
  Inductive assert_sem (p : vlogic) : semCmdType :=
  | assert_ok   : forall Pr s h cl (HP : p s),
    assert_sem p Pr s h cl (t_end s h cl)
  | assert_fail : forall Pr s h cl (HNP : ~p s),
    assert_sem p Pr s h cl t_fail.
  Program Definition assert_cmd p := @Build_semCmd (assert_sem p) _.
(*  Next Obligation.
    intros H; inversion H.
  Qed.*)
  Next Obligation with eauto using assert_sem.
    unfold frame_property; intros.
    inversion HSem; subst...
    + exists (t_end s h cl); split; try repeat constructor; assumption.
    + exists t_fail; split; try repeat constructor; assumption.
  Qed.

  (* |= {p}c{q} *)
  Program Definition sem_triple (p q : psasn) (c : semCmd) : spec :=
    mk_spec (fun P n => forall P' m s h cl STs, Prog_wf_sub P P' -> m <= n -> 
                                           p s STs P' m h ->
       (forall tr, c P' s h cl tr -> Comp P' m STs tr q)
      		
      
    ) _ _.
  Next Obligation.
	eapply H; try eassumption; omega.
  Qed.
  Next Obligation.
	eapply H0; try eassumption. transitivity P'; assumption.
  Qed.
End Commands.


  Local Transparent ILPre_Ops.
  Local Transparent ILFun_Ops.
  
  Add Parametric Morphism : sem_triple with signature
    lentails --> lentails ++> eq ==> lentails
    as sem_triple_entails_m.
  Proof. 
	intros p p' Hp q q' Hq c n x H P m s h cl pr HP Hmn Hp' tr HSem.
	apply Hp in Hp'. 
	specialize (H _ _ _ _ cl pr HP Hmn Hp' tr HSem).
	eapply Comp_entails; eassumption.
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
