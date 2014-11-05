Require Import Program SepAlg SepAlgInsts AssertionLogic SpecLogic SepAlgMap.
Require Import MapInterface MapFacts.
Require Import ILInsts ILogic ILEmbed ILEmbedTac ILQuantTac OpenILogic 
        Open Subst Stack Lang HeapArr BILogic.

Import SepAlgNotations.

Set Implicit Arguments.
Unset Strict Implicit.


Section Commands.

  Variable (P : Program).

  Inductive sem_cmd : stack -> heap -> cmd -> option (stack * heap) -> Prop :=
    | sem_assign s h x v e : 
    	eval e s = v ->
    	sem_cmd s h (cassign x e) (Some (stack_add x v s, h))
    
    | sem_read_fail (ref : ptr) x y f ref (s : stack) (h : heap_ptr) :
        s y = vptr ref ->
        ~ In (ref, f) h ->
        sem_cmd s h (cread x y f) None
    | sem_read (ref : ptr) x y f ref v (s : stack) (h : heap) :
        s y = vptr ref ->
        MapsTo (ref, f) v h ->
        sem_cmd s h (cread x y f) (Some (stack_add x v s, h))
        
    | sem_write_fail x f e s h ref :
        s x = vptr ref ->
        ~ In (ref, f) h ->
        sem_cmd s h (cwrite x f e) None
    | sem_write x f e s h h' ref v :
      s x = vptr ref ->
      In (ref, f) h ->
      eval e s = v ->
      add (ref, f) v h = h' ->
      sem_cmd s h (cwrite x f e) (Some (s, h')).

Require Import Java.Logic.Marshal.
	Check Marshal.

  Inductive sem_comp_cmd : stack -> heap -> comp_cmd -> context -> option (label * stack * heap * context) -> Prop :=
    | sem_atom_fail s h c cont : sem_cmd s h c None -> 
      sem_comp_cmd s h (cc_atom c) cont None
    | sem_atom s h c cont s' h' : sem_cmd s h c (Some (s', h')) -> 
      sem_comp_cmd s h (cc_atom c) cont (Some (l_tau, s', h', cont))
      
  	| sem_skip s h c : sem_comp_cmd s h cc_skip c (Some (l_tau, s, h, c))
  	
  	| sem_send s h a e v hm cont c :
  	  eval e s = v ->
  	  s a = vchan c ->
  	  Marshal P v h hm ->
  	  sem_comp_cmd s h (cc_send a e) cont (Some (l_send c v hm, s, h, cont))
  	  
  	| sem_recv s (h : heap) x a v h hm h'' cont c :
  	  sa_mul h hm h'' ->
  	  s a = vchan c ->
  	  sem_comp_cmd s h (cc_recv x a) cont (Some (l_recv c v hm, stack_add x v s, h'', cont)) 
  	
	| sem_seq_fail s h c1 c2 cont : sem_comp_cmd s h c1 (c2::cont) None -> 
		sem_comp_cmd s h (cc_seq c1 c2) cont None
  	| sem_seq_step s h s' h' c1 c1' c2 cont l : 
  		sem_comp_cmd s h c1 (c2::cont) (Some (l, s', h', c1')) ->
  		sem_comp_cmd s h (cc_seq c1 c2) cont (Some (l, s', h', c1')).

   Inductive sem_par_context : par_context -> label -> par_context -> Prop :=
     | sem_comp_start s h c ctxt c' s' h' ctxt' v : 
        sem_comp_cmd s h c ctxt (Some (l_start v c', s', h', ctxt')) -> 
     	sem_par_context 
     	  (pc_atom s h (c::ctxt)) l_tau
     	  (pc_nu v 
     	      (pc_atom s' h' ctxt) 
     	  	  (pc_atom (fun _ => null) (empty _) (cmd_to_context c')))
     | sem_par_send s h c ctxt s' h' h'' ctxt' v a :
         sem_comp_cmd s h c ctxt (Some (l_send a v h'', s', h', ctxt')) ->
     	 sem_par_context (pc_atom s h (c::ctxt)) (l_send a v h'') (pc_atom s' h' ctxt')
     | sem_par_recv s h c ctxt s' h' h'' ctxt' v a :
         sem_comp_cmd s h c ctxt (Some (l_recv a v h'', s', h', ctxt')) ->
     	 sem_par_context (pc_atom s h (c::ctxt)) (l_recv a v h'') (pc_atom s' h' ctxt')
     | sem_par_tau s h c ctxt s' h' ctxt' :
         sem_comp_cmd s h c ctxt (Some (l_tau, s', h', ctxt')) ->
     	 sem_par_context (pc_atom s h (c::ctxt)) l_tau (pc_atom s' h' ctxt')
     | sem_par_par1 p l p' q c :
         label_channel l <> Some c ->
         sem_par_context p l p' -> sem_par_context (pc_nu c p q) l (pc_nu c p' q)
     | sem_par_par2 p l q q' c :
         label_channel l <> Some c ->
         sem_par_context q l q' -> sem_par_context (pc_nu c p q) l (pc_nu c p q')
     | sem_par_comm1 p a v h p' q q' :
         sem_par_context p (l_send a v h) p' -> 
         sem_par_context q (l_recv a v h) q' ->
         sem_par_context (pc_nu a p q) l_tau (pc_nu a p' q')
     | sem_par_comm2 p a v h p' q q' :
         sem_par_context p (l_recv a v h) p' -> 
         sem_par_context q (l_send a v h) q' ->
         sem_par_context (pc_nu a p q) l_tau (pc_nu a p' q').

  Fixpoint pc_nil pc :=
    match pc with
      | pc_atom _ _ nil => True
      | pc_atom _ _ _ => False
      | pc_nu _ pc1 pc2 => pc_nil pc1 /\ pc_nil pc2
    end.

  Inductive red : nat -> par_context -> Prop := 
    | red_zero pc : red 0 pc
    | red_stop n pc : pc_nil pc -> red n pc
    | red_step n pc1 : (forall pc2 l, sem_par_context pc1 l pc2 -> l = l_tau /\ red n pc2) -> red (S n) pc1.

(*
  Lemma red_tau_step n p q (H : sem_par_context p l_tau q) (Hn : n > 0) :
	  red n p q.
  Proof.
    destruct n; [omega|].
    induction H; simpl in *.
    + eapply red_step; [eapply sem_comp_start; eapply H|].
    + eexists; constructor.
    + exists q. econstructor; [eassumption | constructor].
  Qed.
*)
  Lemma sem_par_hc pc l pc' hc (Hsem : sem_par_context pc l pc') 
    (H : List.Forall (fun c => label_channel l <> Some c) (hc_channels hc)) :
  	sem_par_context (hc_to_pc hc pc) l (hc_to_pc hc pc').
  Proof.
    induction hc; simpl in *.
    + assumption.
    + inversion H; subst; clear H.
      apply Forall_appE in H3 as [H3 _].
      constructor; [|apply IHhc]; assumption.
    + inversion H; subst; clear H.
      apply Forall_appE in H3 as [_ H3].
      constructor; [|apply IHhc]; assumption.
  Qed.

  Lemma sem_par_atom s h c ctxt l s' h' ctxt' 
    (Hl : ~(exists a c, l = l_start a c))
    (Hsem : sem_comp_cmd s h c ctxt (Some (l, s', h', ctxt'))) :
  	sem_par_context (pc_atom s h (c::ctxt)) l (pc_atom s' h' ctxt').
  Proof.
    destruct l; simpl in *.
    + constructor; assumption.
    + constructor; assumption.
    + constructor; assumption.
    + exfalso; apply Hl; exists c0, c1; reflexivity.
  Qed.

  Lemma sem_comp_atom s h c s' h' ctxt
  	(Hsem : sem_cmd s h c (Some (s', h'))) :
  	sem_comp_cmd s h (cc_atom c) ctxt (Some (l_tau, s', h', ctxt)).
  Proof.
    constructor; assumption.
  Qed.

End Commands.

Open Scope open_scope.

Inductive STComp Pr c : ST -> par_context -> Prop :=
  | STComp_tau st pc pc' : 
 	  sem_par_context Pr pc l_tau pc' -> 
 	  STComp Pr c st pc' -> STComp Pr c st pc
  | STComp_send x (P : sasn) st pc v h pc' :
      sem_par_context Pr pc (l_send c v h) pc' ->
      STComp Pr c st pc' ->
      P [{ (fun _ => v) // x }] (fun _ => null) h ->
  	  STComp Pr c (st_send x P st) pc
  | STComp_recv x (P : sasn) st pc :
      (forall v h, P [{ (fun _ => v) // x }] (fun _ => null) h ->
      	exists pc', sem_par_context Pr pc (l_recv c v h) pc' /\ STComp Pr c st pc') ->
      STComp Pr c (st_recv x P st) pc.

  Require Import ExtLib.Core.RelDec.

  Definition protocol := Map [channel, ST].

  Fixpoint st_compatible Pr (c : channel) (hc : hole_context) (st : ST) :=
	match hc with
	  | hc_hole => False
	  | hc_nu1 d hc pc => if c ?[ eq ] d then STComp Pr c st pc else st_compatible Pr c hc st
	  | hc_nu2 d pc hc => if c ?[ eq ] d then STComp Pr c st pc else st_compatible Pr c hc st
	end.

  Definition compatible Pr (hc : hole_context) (p : protocol) :=
  	fold (fun c st acc => st_compatible Pr c hc st /\ acc) p True.

  Program Definition safe (c : comp_cmd) (p : protocol) : spec :=
    mk_spec (fun Pr n ctxt P => forall s h Pr' m hc, P s h -> n >= m -> Prog_sub Pr Pr' ->
        compatible Pr' hc p ->
    	red Pr' m (hc_to_pc hc (pc_atom s h (cmd_to_context c ++ ctxt)))) _ _ _.
  Next Obligation.
	eapply H0; try eassumption. transitivity P'; assumption.
  Qed.
  Next Obligation.
	destruct H as [R [_ H]].
	specialize (H _ _ H1).
	destruct H as [h1 [h2 [HSub [HT HR]]]].
	specialize (H0 _ _ _ _ hc HT H2 H3 H4).
	admit.
 Qed.


Definition triple P p c Q p' :=
	|-- safe cc_skip p' @ Q -->> safe c p @ P.

    Transparent ILPre_Ops.
    Transparent ILFun_Ops.
    Require Import IBILogic.
    Require Import BILInsts.
    Transparent BILPre_Ops.
    Transparent BILFun_Ops.
    
    Opaque MapSepAlgOps.
Require Import Model.
Require Import ExtLib.Tactics.Consider.

Lemma compatible_hole Pr pr (H : compatible Pr hc_hole pr) : pr === empty ST.
Proof.
  revert H; unfold compatible.
  apply fold_rec. intros.
  intros c. admit.
  intros.
  destruct H3. simpl in H3. destruct H3.
Qed.
(*
Lemma compatible_nu1_ineq Pr c d hc pc p (H : compatible Pr (hc_nu1 c hc pc) p) 
	(HMapsTo : In d p) (Hineq : c <> d) : compatible Pr hc p.
Proof.
  unfold compatible in H.
 o *)


Lemma send_triple (x y : var) (e : dexpr) st p P Q (v : channel) 
  (HPQ : P |-- Q) (Hembed : P |-- embed (open_eq x/V `(vchan v))) 
  (Hp : MapsTo v (st_send y Q st) p) :
  triple P p (cc_send x e) P (add v st p).
Proof.
  intros Pr k ctx T _ Pr' HPr n Hkn R HR Hsafe s h Pr'' m hc HPR Hnm Hpr Hcomp.
  simpl. destruct m; [constructor|].
  apply red_step. intros. simpl in H.
  simpl in Hsafe.
  admit. (* I believe you, but you need a lot of work *)
Qed.

Lemma start_triple p x c v P st
  (H : triple ltrue (add v st (empty ST)) c ltrue (empty ST)) :
	triple P p (cc_start x c) P (add v (dual st) p).
Proof.
  intros Pr k ctx T _ Pr' HPr n Hkn R HR Hsafe s h Pr'' m hc HPR Hnm Hpr Hcomp.
  simpl; destruct m; [constructor|].
  apply red_step. intros. simpl in H0.
  assert ((@ltrue spec _) Pr k nil T) as HTrue by apply I.
  assert (Prog_sub Pr Pr) as HPr2 by reflexivity.
  assert (k >= k) as Hk by omega.
  assert (extSP T T) as HTT by admit.
  assert ((safe cc_skip (empty ST) @ ltrue) Pr k nil T) as blurb.
  simpl; intros. constructor. admit (* not true *).
  specialize (H Pr k nil T HTrue Pr HPr2 k Hk T HTT blurb).
  simpl in H.
  
Lemma write_lemma (x : var) (f : field) (e : dexpr) :
	@lentails spec _
	(safe cc_skip @ (`pointsto (x/V) (`f) (eval e)))
	(safe (cc_atom (cwrite x f e)) @ (Exists v, `pointsto (x/V) (`f) v)).
Proof.
  intros Pr k cont hc T Hsafe s h n HT Hkn. 
  destruct HT as [h1 [h2 [Hord [[v [H1 [H2 [hframe H3]]]] H4]]]].
  unfold var_expr, liftn, lift in H1, H2, H3; simpl in H1, H2, H3.
  eapply red_tau_step.  
  eapply sem_par_hc.
  eapply sem_par_atom; [intros [a [b H]]; congruence |].
  eapply sem_comp_atom.
  eapply sem_write with (ref := val_to_ptr (s x)).
  destruct (s x); simpl in *; try intuition congruence.
  eapply (@sa_mul_inL _ _ _ _ _ _ _ _ (val_to_ptr (s x), f)) in H3.
  destruct H3 as [H3 H5].
  eapply (@sa_mul_inL _ _ _ _ _ _ _ _ (val_to_ptr (s x), f)) in Hord.
  intuition congruence.
  apply H5.
  admit. reflexivity.
  reflexivity.
Qed.
*)
  Lemma test_seq (c1 c2 : comp_cmd) (P Q R : sasn) (p q r : protocol)
  	(Hc1 : safe cc_skip q @ Q |-- safe c1 p @ P) 
  	(Hc2 : safe cc_skip r @ R |-- safe c2 q @ Q) :
  	safe cc_skip r @ R |-- safe (cc_seq c1 c2) p @ P.
  Proof.
    
 
   Lemma safe_skip S c P (p : protocol) (H : S |-- safe c p @ P) :
    	S |-- safe (cc_seq cc_skip c) p @ P.
    Proof.
      intros Pr k cont hc T Hsafe s h Pr' n HT Hkn HPr Hcomp.
      simpl in Hkn; simpl. eapply H; eassumption.
    Qed.
      
    Lemma noethu S c1 c2 c3 P Q p q
    	(Hc1 : safe c2 q @ Q |-- safe c1 p @ P)
    	(H : S |-- safe (cc_seq c2 c3) q @ Q) :
    	S |-- safe (cc_seq c1 c3) p @ P.
    Proof.
      intros Pr k c T Hsafe s h Pr' n hc HT Hkn HPr Hcomp.
      simpl. rewrite <- app_assoc.
      specialize (Hc1 Pr k (cmd_to_context c3 ++ c)).
      eapply Hc1; [| eapply HT | omega | eapply HPr | eapply Hcomp].
      simpl; simpl in H; intros. rewrite app_assoc.
      eapply H; [eapply Hsafe | eapply H0 | omega | apply H2 | eapply H3].
	Qed.
    
    
    
    eapply noethu; [eassumption|].
    eapply safe_skip. assumption.	
    Qed.
      rewrite app_length.
      Focus 3. omega.

    intros Pr k c T Hsafe s h n HT Hkn.
    specialize (Hc2 _ _ _ _ Hsafe).
  	
	Lemma blurb P c1 c2 : safe @ P @!(cseq c1 c2) |-- safe @ P @! c2.
	Proof.
	  intros Pr n cnt Q H s h m HP Hnm. simpl in H.
	  assert (n + (length (cmd_to_context c1) + length (cmd_to_context c2)) >=
	  	      m + length (cmd_to_context c1)) as Hnm' by omega.
	  rewrite app_length in H. 
	  specialize (H _ _ _ HP Hnm').
	  destruct H as [s' [h' HRun]].
      admit.
    Qed.
    assert ((safe @ Q @! (cseq c2 cskip)) Pr k c T) by (simpl; rewrite app_nil_r; apply Hc2).
    apply blurb in H. specialize (Hc1 _ _ _ _ H).
    simpl in H.
    simpl in *. specialize (Hc1 s h m 
    simpl.
    rewrite blurb.
	  assert (ext_cont (cmd_to_context c ++ cnt) cont).
	  	destruct Hcont; subst. simpl in *. rewrite H0.
	  	exists 
	  specialize (H _ _ _ _ HP Hnm Hcont).
	simpl in Hc2.

    Lemma safe_ext (c1 c2 : cmd) :
    	safe (cseq c1 c2) |-- safe c1.
    Proof.
      intros Pr n cnt P H.
      intros s h m HP Hnm Hcont.
      
      assert (safe c1 Pr n (cnt ++ cmd_to_context c2) P -> safe c1 Pr n cnt P).
      intros. solve_model H0. eexists; reflexivity.
      apply H0. clear H0. intros s h m HP Hnm Hcont.
      simpl in H.
      assert (ext_cont cnt (cmd_to_context c1 ++ cmd_to_context c2)).
      destruct Hcont.
	  admit.
	  admit.
    Qed.
    (*
    Lemma safe_ext (c1 c2 : cmd) :
    	safe (cseq c1 c2) |-- safe c1.
    Proof.
      intros Pr n cnt P H s h m HP Hnm.
      specialize (H _ _ _ HP Hnm). 
      destruct H as [cont' [s' [h' [[cont'' Hcont] Hrun]]]].
      exists (cmd_to_context c2 ++ cont'), s', h'; split; [|rewrite app_assoc; apply Hrun].
      exists (cmd_to_context c2 ++ cont''). rewrite Hcont. rewrite <- app_assoc. reflexivity.
    Qed.
    *)
    assert ((safe (cseq cskip c2) @ Q) Pr k c T) by (apply Hc2).
    rewrite safe_ext in H. specialize (Hc1 _ _ _ _ H).
    specialize (Hc1 _ _ _ HT Hkn).
    apply Hc1.
    destruct Hcont. eexists. rewrite H0. simpl.
    rewrite <- app_assoc. reflexivity.
    destruct Hc1 as [cont' [s' [h' [Hcont Hrun]]]].
    unfold ext_cont in Hcont.
    simpl in Hc2.
    assert ((Q ** T) s' h') by admit.
    specialize (Hc2 _ _ _ H0 Hkn).
    destruct Hc2 as [c'' [s'' [h'' [Hcont2 Hrun2]]]].
    simpl in Hc2.
    exists (cmd_to_context c2
      destruct Hcont as [cont'' Hcont].
      destruct H as [s' [h' H]]. clear -H.
      simpl in *. rewrite <- app_assoc in H.
      
      generalize dependent c1; generalize dependent c2.
      induction cnt'; intros; simpl in *.
      admit.
      destruct H.
      destruct Hcnt as [cnt'' Hcnt].
      rewrite Hcnt in H. simpl in *.
      specialize (H _ _ _ nil HP Hnm).
       rewrite <- Hcnt.
      assert (ext_cont cnt (c2::cnt')) as H1. {
      	exists (c2::cnt''). rewrite <- Hcnt; reflexivity.
      }
      specialize (H _ _ _ _ HP Hnm H1).
      destruct H as [s' [h' H]]. rewrite <- Hcnt in H.
      admit.
    Qed.
    simpl in Hc2.
    Lemma test (c1 c2 c3 : cmd) (P Q : sasn) (H : safe c1 @ P |-- safe c2 @ Q) :
    	safe (cseq c1 c3) @ P |-- safe (cseq c2 c3) @ Q.
    Proof.
      intros Pr k c T Hsafe s h n cont HT Hkn Hcont.
      simpl in Hsafe.
    specialize 
      destruct (H s h m).
      specialize (H _ _ _ _ HP Hnm Hcnt).
      destruct Hcnt as [cnt'' Hcnt]. rewrite <- Hcnt.
      destruct H as [s' [h' H]].
      rewrite <- Hcnt in H. exists s', h'.
      exists s', h'.
      destruct Hcnt as [cnt'' Hcnt]. rewrite <- Hcnt.
      specialize (H _ _ _ _ HP Hnm Hcnt).
      assert (ext_cont cnt (cnt' ++ (c::nil))). exists (cnt'' ++ (c::nil)).
      rewrite <- Hcnt. simpl. rewrite app_assoc. reflexivity.
      specialize (H _ _ _ _ HP Hnm H0).
      destruct H as [s' [h' H]].
      exists s', h'.
      simpl in H.
      simpl in *.
    
    assert (safe c1
    simpl in Hc1.
    simpl in Hsafe.
    simpl in Hc2.
    simpl in Hc1.
    specialize (Hc1 _ _ _ _ Hc2).
  
  Lemma test_write (x : var) (f : field) (e : dexpr) : 
    @lentails spec _ 
    (safe cskip @ (`pointsto x/V `f (eval e)))
  	((safe (cwrite x f e)) @ (@lexists sasn _ val (fun v => `pointsto x/V `f `v))).
  Proof.
    Transparent ILPre_Ops.
    Transparent ILFun_Ops.
    intros Pr k c Q HS s h n HQ Hkn.
    destruct n. admit.
    destruct HQ as [h1 [h2 [Hsub [[v [H1 H2]] H3]]]].
    simpl in H1, H2.
    unfold liftn, lift in H2; simpl in H2.
    destruct h, h1.
    unfold var_expr in H1.
    assert (exists ref, s x = vptr ref) by admit.
    destruct H as [ref H].
    simpl in HS.
    specialize (HS s (h1, h0) (S n)).
    assert (exists (s' : stack) (h' : heap), run s (h1, h0) cskip (S n) c s' h') by admit.
    destruct H0 as [s'' [h'' H0]].
    inversion H0; subst.
    exists cskip.
    split; [|constructor].
    eapply sem_write; try reflexivity; try eassumption.
    eapply run_step; [|eapply run_skip].
    eapply sem_write; try reflexivity; try eassumption.
    simpl in HQ.
    destruct HQ.
    exists (cwrite x f e), s, h; constructor.
    exists cskip, s. destruct h.
    assert (exists ref, s x = vptr ref) by admit. destruct H as [ref H].
    exists (add (ref, f) (eval e s) h, h0).
    eapply run_step; [|eapply run_skip].
    eapply sem_write; try reflexivity; 
    try eassumption.
    constructor.
    simpl in *.
    exists cskip, s.
	destrcut H.
	simpl in H.
	assert (S k >= m) by omega.
	destruct (H _ _ _ H0 H2) as [c' [s' [h' HR]]]; clear H.
	inversion HR; subst.
	exists cskip, s', h'. constructor.
	clear HR.
	induction c; inversion H3; try congruence; subst.
	
	exists cskip, s'0, h'0. constructor.
    admit.
  Qed.
  Next Obligation.
	unfold extSP in H.
	destruct H as [R [_ H]].
	specialize (H _ _ H1). 
	Require Import BILInsts IBILogic.
	Transparent SAIBIOps BILFun_Ops.
	destruct H as [h1 [h2 [Hstar [Hh1 Hh2]]]].
	assert (k >= k) as Hk by omega.
	specialize (H0 _ _ _ Hh1 Hk).
	apply H0.
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