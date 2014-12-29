Require Import Program SepAlg SepAlgInsts AssertionLogic SpecLogic SepAlgMap.
Require Import MapInterface MapFacts.
Require Import ILInsts ILogic ILEmbed ILEmbedTac ILQuantTac OpenILogic 
        Open Subst Stack Lang HeapArr BILogic.
        
Require Import SessionType ProtocolLogic.

Require Import ExtLib.Tactics.Consider.

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
	
  Definition channels := list channel.

  Inductive sem_comp_cmd : stack -> heap -> channels -> comp_cmd -> context -> 
    option (label * stack * heap * context) -> Prop :=
    | sem_atom_fail s h c cs cont : sem_cmd s h c None -> 
      sem_comp_cmd s h cs (cc_atom c) cont None
    | sem_atom s h c cs cont s' h' : sem_cmd s h c (Some (s', h')) -> 
      sem_comp_cmd s h cs (cc_atom c) cont (Some (l_tau, s', h', cont))
      
  	| sem_skip s h cs c : sem_comp_cmd s h cs cc_skip c (Some (l_tau, s, h, c))
  	
  	| sem_send s h a e v hm cs cont c :
  	  eval e s = v ->
  	  s a = vchan c ->
  	  Marshal P v h hm ->
  	  sem_comp_cmd s h cs (cc_send a e) cont (Some (l_send c v hm, s, h, cont))
  	  
  	| sem_recv s (h : heap) x a v h hm h'' cs cont c :
  	  sa_mul h hm h'' ->
  	  s a = vchan c ->
  	  sem_comp_cmd s h cs (cc_recv x a) cont (Some (l_recv c v hm, stack_add x v s, h'', cont)) 
  	  
  	| sem_start s h x y c v cs cont :
  	  ~ List.In v cs ->
  	  sem_comp_cmd s h cs (cc_start x y c) cont (Some (l_start v y c, stack_add x (vchan v) s, h, cont))
  	
	| sem_seq_fail s h c1 c2 cs cont : sem_comp_cmd s h cs c1 (c2::cont) None -> 
		sem_comp_cmd s h cs (cc_seq c1 c2) cont None
  	| sem_seq_step s h s' h' c1 c1' c2 cs cont l : 
  		sem_comp_cmd s h cs c1 (c2::cont) (Some (l, s', h', c1')) ->
  		sem_comp_cmd s h cs (cc_seq c1 c2) cont (Some (l, s', h', c1')).

   Inductive sem_par_context : channels -> par_context -> label -> par_context -> Prop :=
     | sem_comp_start s h c ctxt c' s' h' ctxt' v x cs : 
        sem_comp_cmd s h cs c ctxt (Some (l_start v x c', s', h', ctxt')) -> 
     	sem_par_context (v::cs)
     	  (pc_atom s h (c::ctxt)) l_tau
     	  (pc_nu v 
     	      (pc_atom s' h' ctxt') 
     	  	  (pc_atom (stack_add x (vchan v) (stack_empty _ _)) (empty _) (cmd_to_context c')))
     | sem_par_send s h c ctxt s' h' h'' ctxt' v a cs :
         sem_comp_cmd s h cs c ctxt (Some (l_send a v h'', s', h', ctxt')) ->
     	 sem_par_context cs (pc_atom s h (c::ctxt)) (l_send a v h'') (pc_atom s' h' ctxt')
     | sem_par_recv s h c ctxt s' h' h'' ctxt' v a cs :
         sem_comp_cmd s h cs c ctxt (Some (l_recv a v h'', s', h', ctxt')) ->
     	 sem_par_context cs (pc_atom s h (c::ctxt)) (l_recv a v h'') (pc_atom s' h' ctxt')
     | sem_par_tau s h c ctxt s' h' ctxt' cs :
         sem_comp_cmd s h cs c ctxt (Some (l_tau, s', h', ctxt')) ->
     	 sem_par_context cs (pc_atom s h (c::ctxt)) l_tau (pc_atom s' h' ctxt')
     | sem_par_par1 p l p' q c cs :
         label_channel l <> Some c ->
         sem_par_context (c::cs) p l p' -> sem_par_context cs (pc_nu c p q) l (pc_nu c p' q)
     | sem_par_par2 p l q q' c cs :
         label_channel l <> Some c ->
         sem_par_context (c::cs) q l q' -> sem_par_context cs (pc_nu c p q) l (pc_nu c p q')
     | sem_par_comm1 p a v h p' q q' cs :
         sem_par_context cs p (l_send a v h) p' -> 
         sem_par_context cs q (l_recv a v h) q' ->
         sem_par_context cs (pc_nu a p q) l_tau (pc_nu a p' q')
     | sem_par_comm2 p a v h p' q q' cs :
         sem_par_context cs p (l_recv a v h) p' -> 
         sem_par_context cs q (l_send a v h) q' ->
         sem_par_context cs (pc_nu a p q) l_tau (pc_nu a p' q').

  Fixpoint pc_nil pc :=
    match pc with
      | pc_atom _ _ nil => True
      | pc_atom _ _ _ => False
      | pc_nu _ pc1 pc2 => pc_nil pc1 /\ pc_nil pc2
    end.

  Inductive red : nat -> par_context -> Prop := 
    | red_zero pc : red 0 pc
    | red_stop n pc : pc_nil pc -> red n pc
    | red_step n pc1 : (forall cs pc2, sem_par_context cs pc1 l_tau pc2 -> red n pc2) -> red (S n) pc1.


  Lemma red_dc n pc m (H : red n pc) (Hmn : m <= n) : red m pc.
  Proof.
    generalize dependent m; induction H; intros.
    + inversion Hmn; apply red_zero.
    + apply red_stop; assumption.
    + destruct m; [apply red_zero|].
      apply red_step; intros; eapply H0; [eassumption | omega].
  Qed.

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
(*
  Lemma sem_par_hc cs pc l pc' hc (Hsem : sem_par_context cs pc l pc') 
    (H : List.Forall (fun c => label_channel l <> Some c) (hc_channels hc)) :
  	sem_par_context cs (hc_to_pc hc pc) l (hc_to_pc hc pc').
  Proof.
    generalize dependent cs.
    induction hc; simpl in *; intros.
    + assumption.
    + inversion H; subst; clear H.
      apply Forall_appE in H3 as [H3 _].
      constructor; [|apply IHhc]; try assumption.
      clear -Hsem H2.
      induction Hsem.
      simpl in *.
      assert (sem_par_context (v :: c :: cs) (pc_atom s h (c0 :: ctxt)) l_tau
  (pc_nu v (pc_atom s' h' ctxt')
     (pc_atom (stack_add x (vchan v) (@stack_empty var val _)) (empty val)
        (cmd_to_context c')))).
      apply sem_comp_start.
      assumption.
      constructor.
    + inversion H; subst; clear H.
      apply Forall_appE in H3 as [_ H3].
      constructor; [|apply IHhc]; assumption.
  Qed.

  Lemma sem_par_atom s h cs c ctxt l s' h' ctxt' 
    (Hl : ~(exists a x c, l = l_start a x c))
    (Hsem : sem_comp_cmd s h cs c ctxt (Some (l, s', h', ctxt'))) :
  	sem_par_context cs (pc_atom s h (c::ctxt)) l (pc_atom s' h' ctxt').
  Proof.
    destruct l; simpl in *.
    + constructor; assumption.
    + constructor; assumption.
    + constructor; assumption.
    + exfalso; apply Hl; exists c0, v, c1; reflexivity.
  Qed.
*)
  Lemma sem_comp_atom s h cs c s' h' ctxt
  	(Hsem : sem_cmd s h c (Some (s', h'))) :
  	sem_comp_cmd s h cs (cc_atom c) ctxt (Some (l_tau, s', h', ctxt)).
  Proof.
    constructor; assumption.
  Qed.

End Commands.

Open Scope open_scope.
Check all_STs.

Definition protocol_empty (p : protocol) :=
  for_all (fun _ e => match e with | st_end => true | _ => false end) p = true.

Inductive STComp (Pr : Program) : nat -> protocol -> par_context-> Prop :=
  | STComp_zero p pc : STComp Pr 0 p pc
  | STComp_nil n p pc : pc_nil pc -> protocol_empty p -> STComp Pr n p pc
  | STComp_step n p pc : 
    (forall l pc' cs, sem_par_context Pr cs pc l pc' -> 
      STComp_aux Pr n p l pc') -> 
    STComp Pr (S n) p pc
with STComp_aux (Pr : Program) : nat -> protocol -> label -> par_context -> Prop :=
  | STComp_tau n p pc : STComp Pr n p pc -> STComp_aux Pr n p l_tau pc
  | STComp_send n x c (P : sasn) p st pc v h :
      MapsTo c (st_send x P st) p ->
      P [{ (fun _ => v) // x }] (fun _ => null) h ->
      STComp Pr n (add c st p) pc ->
      STComp_aux Pr n p (l_send c v h) pc
  | stComp_recv n x c (P : sasn) p st pc v h :
      MapsTo c (st_recv x P st) p ->
      (P [{ (fun _ => v) // x }] (fun _ => null) h -> STComp Pr n (add c st p) pc) ->
      STComp_aux Pr n p (l_recv c v h) pc.
      
  Definition compatible Pr n (hc : hole_context) (p : protocol) :=
    forall pc m, m <= n -> STComp Pr m p pc -> red Pr m (hc_to_pc hc pc).

  Program Definition safe (c : comp_cmd) p : spec :=
    mk_spec (fun Pr n ctxt P => forall s h Pr' m hc, P s h -> n >= m -> Prog_sub Pr Pr' ->
        compatible Pr' m hc p ->
    	red Pr' m (hc_to_pc hc (pc_atom s h (cmd_to_context c ++ ctxt)))) _ _ _.
  Next Obligation.
	eapply H0; try eassumption. transitivity P'; assumption.
  Qed. (*
  Next Obligation.
    eapply H0; try eassumption; omega. 
  Qed.*)
  Next Obligation.
	destruct H as [R [_ H]].
	specialize (H _ _ H1).
	destruct H as [h1 [h2 [Hsub2 [HT HR]]]].
	specialize (H0 _ _ _ _ hc HT H2 H3 H4).
	generalize dependent (cmd_to_context c ++ c0); clear c c0; intros cnt Hcnt.
	generalize dependent p.
	remember (hc_to_pc hc (pc_atom s h1 cnt)).
	induction Hcnt; intros.
	+ constructor.
	+ constructor. admit.
	+ subst. apply red_step; intros.
	  admit.
	  (*
	  eapply H with cs.
	  clear -H5.
	  induction H5.
	  generalize dependent cs.
	  induction hc; simpl; intros.
	  admit.
	  inversion H5; subst.
	  apply sem_par_par1. assumption. eapply H7.
	  Print sem_par_context.
	  apply sem_par1.
	induction hc; simpl; simpl in Hcnt; intros.
	admit.
	generalize dependent c0.
	induction c; simpl; intros.
	destruct c; simpl in H0.
	admit.
*)
 Qed.
(*
  Program Definition safe2 (c : comp_cmd) : spec :=
    mk_spec (fun Pr n _ P => forall s p h Pr' m hc, P s p h -> n >= m -> Prog_sub Pr Pr' ->
        compatible Pr' m hc p ->
    	red Pr' m (hc_to_pc hc (pc_atom s h (cmd_to_context c)))) _ _ _.
  Next Obligation.
    eapply H; try eassumption; omega.
  Qed.
  Next Obligation.
	eapply H0; try eassumption. transitivity P'; assumption.
  Qed.
  Next Obligation.
	destruct H as [R [_ H]].
	specialize (H _ _ _ H1).
	destruct H as [p1 [p2 [HSub1 [h1 [h2 [Hsub2 [HT HR]]]]]]].
	specialize (H0 _ _ _ _ _ hc HT H2 H3).
	admit.
 Qed.
*)
    Transparent ILPre_Ops.
    Transparent ILFun_Ops.
    Require Import IBILogic.
    Require Import BILInsts.
    Transparent BILPre_Ops.
    Transparent BILFun_Ops.
    

Program Definition st_safe x c st :=
  mk_spec (fun Pr n _ P => forall v,
    let s := stack_add x (vchan v) (stack_empty _ _) in
    let h := empty val in
    let p := add v st (empty ST) in
    forall Pr' m hc, P s h ->
    n >= m -> Prog_sub Pr Pr' ->
      compatible Pr' m hc p ->
      red Pr' m (hc_to_pc hc (pc_atom s h (cmd_to_context c)))) _ _ _.
Next Obligation.
  eapply H0; try eassumption.
  + transitivity P'; assumption.
Qed.
Next Obligation.
  apply H0; try assumption.
  destruct H as [R H].
  admit.
Qed.

Definition triple P p c Q q : spec :=
	safe cc_skip q @ Q -->> safe c p @ P.

    Opaque MapSepAlgOps.
Check safe.
Print triple.
(*
Lemma verify_st v x c p
  (H : @lentails spec _ ltrue (safe c (add v p (empty ST)) @ (embed (open_eq x/V `(vchan v))))) :
  |-- st v x c p.
*)

Lemma extSP_id P : extSP P P.
Proof.
  exists empSP; rewrite empSPR; reflexivity.
Qed.

(*
Lemma verify_st x c p
  (H : forall v, @lentails spec _ ltrue (triple (embed (open_eq x/V `(vchan v))) (add v p (empty ST)) c ltrue (empty ST))) :
  |-- st x c p.
Proof.
  intros Pr m ctx Q _ v Pr' n hc HQ Hmn HPr Hcomp.
  specialize (H v Pr m nil Q I).
  simpl in H.
  rewrite app_nil_r in H.
  eapply H; [eassumption | eassumption | apply extSP_id | | | reflexivity | reflexivity|].
  + intros. 
    eapply H3 with (m := m0). 
    reflexivity.
    admit. (* add case that empty session type is compatible with the 0 process *)
  + 
  exists ((empty val):heap), ((empty val):heap).
  eexists. admit.
  split; [|assumption].
  unfold open_eq, var_expr, liftn, lift; simpl.
  rewrite stack_lookup_add. reflexivity.
  + admit.
Qed.
*)
Require Import Model.
Require Import ExtLib.Tactics.Consider.
(*
Lemma compatible_holeR Pr pr (H : compatible Pr hc_hole pr) : Empty pr.
Proof.
  revert H; unfold compatible.
  apply fold_rec; intros; [assumption|].
  destruct H3. simpl in H3. destruct H3.
Qed.

Lemma compatible_holeL Pr (pr : protocol) (H : Empty pr) : compatible Pr hc_hole pr.
Proof.
  revert H; unfold compatible. 
  apply fold_rec; intros; [apply I|].
  specialize (H1 k); specialize (H3 k e).
  rewrite find_mapsto_iff in H3.
  contradiction H3. rewrite H1.
  apply add_eq_o; reflexivity.
Qed.

Lemma compatible_nu1 Pr c hc pc p (H : compatible Pr (hc_nu1 c hc pc) p) 
	 : compatible Pr hc (filter (fun k _ => negb (k ?[ eq ] c)) p).
Proof.
  unfold compatible.
  assert (exists m, m === filter (fun k _ => negb (k ?[ eq ] c)) p) by (eexists; reflexivity).
  destruct H0 as [m H0]. 
  assert (fold
  (fun (c0 : channel) (st0 : ST) (acc : Prop) =>
   st_compatible Pr c0 hc st0 /\ acc)
  m True).

  generalize dependent p; apply fold_rec_weak; intros. 
  admit.
  apply I.
  specialize (H0 (remove k p)).
  split; [|apply H0].
  
  simpl.
  Print Add.
  
  Check remove.
  rewrite H4 in H1.
  split; [|eapply H2; [eassumption|]].
  unfold Add in H1.
  Print Add.
  SearchAbout fold Add.
  unfold compatible in H1.

  rewrite fold_add with (eqA := iff) in H1; try assumption.
  split; [|apply H0; apply H1].
  destruct H1.
  simpl in H1.
  consider (k ?[ eq ] c); intros; subst; [|assumption].
  consider (k ?[ eq ] c); intros; subst; [|assumption].
  admit.
  unfold st_compatible.
  inversion H1.
  apply _.
  intros c1 c2 Hc s1 s2 Hs a1 a2 Ha; subst; intuition congruence.
  unfold transpose_neqkey; intuition congruence.
  apply _.
  Focus 4.
  unfold transpose_neqkey. intros ;simpl.
  intros. intuition congruence.
  revert H. apply fold_rec. intros.
  eapply compatible_holeL in H.
  induction p. simpl.
 o *)


Lemma hc_to_pc Pr hc l cs pc pc'
  (H : sem_par_context Pr cs (hc_to_pc hc pc) l pc') :
  (exists hc', (forall pc, sem_par_context Pr cs (hc_to_pc hc pc) l (hc_to_pc hc' pc)) /\
    pc' = hc_to_pc hc' pc)  \/
  (exists pc'' cs', sem_par_context Pr (cs' ++ cs) pc l pc'' /\
      pc' = hc_to_pc hc pc'')(* \/
  (exists hc' cs' pc'' hc'' hc''' c v h, 
    sem_par_context Pr (cs ++ cs') (hc_to_pc hc' pc) l (hc_to_pc hc'' pc'') /\
    sem_par_context Pr (cs ++ cs') pc (l_send c v h) pc'' /\
    (forall pc, sem_par_context Pr (cs ++ cs') (hc_to_pc hc' pc) (l_recv c v h) (hc_to_pc hc'' pc)) /\
    l = l_tau /\ hc = insert_context hc''' hc' /\ pc' = hc_to_pc hc''' (hc_to_pc hc'' pc'')) \/
  (exists hc' cs' pc'' hc'' c v h, 
    sem_par_context Pr (cs ++ cs') (hc_to_pc hc' pc) l (hc_to_pc hc'' pc'') /\
    sem_par_context Pr (cs ++ cs') pc (l_send c v h) pc'' /\
    (forall pc, sem_par_context Pr (cs ++ cs') (hc_to_pc hc' pc) (l_recv c v h) (hc_to_pc hc'' pc)) /\
    l = l_tau).*)

      
  (*
  (exists v x c' s' h' ctx', sem_comp_cmd Pr s h cs c ctx (Some (l_start v x c', s', h', ctx')) /\
    pc = hc_to_pc hc (pc_nu v (pc_atom s' h' ctx')
      (pc_atom (stack_add x (vchan v) (stack_empty _ _)) (empty _) (cmd_to_context c'))) /\
    l = l_tau) \/
  (exists hc' a v h', 
    (forall s h'', sem_par_context Pr cs (hc_to_pc hc (pc_atom s h'' nil)) (l_send a v h')
      (hc_to_pc hc' (pc_atom s h'' nil))) /\
    (exists s' h'' ctx', sem_comp_cmd Pr s h cs c ctx (Some (l_recv a v h', s', h'', ctx')) /\
    pc = hc_to_pc hc' (pc_atom s' h'' ctx') /\ l = l_tau)) \/
  (exists hc' a v h', 
    (forall s h'', sem_par_context Pr cs (hc_to_pc hc (pc_atom s h'' nil)) (l_recv a v h')
      (hc_to_pc hc' (pc_atom s h'' nil))) /\
    (exists s' h'' ctx', sem_comp_cmd Pr s h cs c ctx (Some (l_send a v h', s', h'', ctx')) /\
    pc = hc_to_pc hc' (pc_atom s' h'' ctx') /\ l = l_tau))*).
Proof.
  admit.
  (*
  remember (hc_to_pc hc (pc_atom s h (c :: ctx))).
  generalize dependent hc.
  induction H; intros.
  + destruct hc; simpl in Heqp; inversion Heqp; subst; clear Heqp.
    subst. right. right. left.
    exists v, x, c', s', h', ctxt'.
    repeat split; assumption.
  + destruct hc; simpl in Heqp; inversion Heqp; subst.
    right. left.
    exists s', h', ctxt'.
    simpl; split; [assumption | reflexivity].
  + destruct hc; simpl in Heqp; inversion Heqp; subst.
    right. left.
    exists s', h', ctxt'.
    simpl; split; [assumption | reflexivity].
  + destruct hc; simpl in Heqp; inversion Heqp; subst.
    right. left.
    exists s', h', ctxt'.
    simpl; split; [assumption | reflexivity].
  + destruct hc; simpl in Heqp; inversion Heqp; subst.
    * specialize (IHsem_par_context _ eq_refl).
	  destruct IHsem_par_context as [[hc' [H1 H2]] | [[s'' [h' [ctx' [H1 H2]]]] | 
	    [[v' [z [c' [s'' [h' [ctx' [H1 [H2 H3]]]]]]]] | 
	  	[[hc' [b [v' [h' [H1 [s'' [h'' [ctx' [H2 [H3 H4]]]]]]]]]] |
	  	[hc' [b [v' [h' [H1 [s'' [h'' [ctx' [H2 [H3 H4]]]]]]]]]]]]]].
      - subst. left. exists (hc_nu1 c1 hc' p0).
        simpl; split; [|reflexivity].
        intros. constructor; [assumption | apply H1].
      - subst; right; left.
        exists s'', h', ctx'.
        split; [assumption | reflexivity].
      - subst; right; right; left; repeat eexists; assumption.
      - subst; right; right; right; left. 
        exists (hc_nu1 c1 hc' p0), b, v', h'. simpl.
        split; intros. constructor. simpl.
        admit. (* Name clash *)
        apply H1.
        repeat eexists; eassumption.
      - subst; right; right; right; right.
        exists (hc_nu1 c1 hc' p0), b, v', h'. simpl.
        split; intros. constructor. simpl.
        admit. (* Name clash *)
        apply H1.
        repeat eexists; eassumption.
    * left. exists (hc_nu2 c1 p' hc).
      split; [|reflexivity].
      intros. constructor; assumption.
  + destruct hc; simpl in Heqp; inversion Heqp; subst; simpl.
    left. exists (hc_nu1 c1 hc q'). simpl; intros; split; [|reflexivity].
    intros; constructor; assumption.
   * specialize (IHsem_par_context _ eq_refl).
	  destruct IHsem_par_context as [[hc' [H1 H2]] | [[s'' [h' [ctx' [H1 H2]]]] | 
	    [[v' [z [c' [s'' [h' [ctx' [H1 [H2 H3]]]]]]]] | 
	  	[[hc' [b [v' [h' [H1 [s'' [h'' [ctx' [H2 [H3 H4]]]]]]]]]] |
	  	[hc' [b [v' [h' [H1 [s'' [h'' [ctx' [H2 [H3 H4]]]]]]]]]]]]]].
      - subst. left. exists (hc_nu2 c1 p0 hc').
        simpl; split; [|reflexivity].
        intros. constructor; [assumption | apply H1].
      - subst; right; left.
        exists s'', h', ctx'.
        split; [assumption | reflexivity].
      - subst; right; right; left; repeat eexists; assumption.
      - subst; right; right; right; left. 
        exists (hc_nu2 c1 p0 hc'), b, v', h'. simpl.
        split; intros. constructor. simpl.
        admit. (* Name clash *)
        apply H1.
        repeat eexists; eassumption.
      - subst; right; right; right; right.
        exists (hc_nu2 c1 p0 hc'), b, v', h'. simpl.
        split; intros. constructor. simpl.
        admit. (* Name clash *)
        apply H1.
        repeat eexists; eassumption.
  + destruct hc; simpl in Heqp; inversion Heqp; subst; clear Heqp.
    * specialize (IHsem_par_context1 _ eq_refl); clear IHsem_par_context2.
	  destruct IHsem_par_context1 as [[hc' [H1 H2]] | [[s'' [h' [ctx' [H1 H2]]]] | 
	    [[v' [z [c' [s'' [h' [ctx' [H1 [H2 H3]]]]]]]] | 
	  	[[hc' [b [v' [h' [H1 [s'' [h'' [ctx' [H2 [H3 H4]]]]]]]]]] |
	  	[hc' [b [v' [h' [H1 [s'' [h'' [ctx' [H2 [H3 H4]]]]]]]]]]]]]]; try congruence; subst.
      - subst. left. exists (hc_nu1 c0 hc' q'); simpl.
        simpl; split; intros; [|reflexivity].
        eapply sem_par_comm1; [apply H1|eassumption].
      - subst; right; right; right; right. simpl. exists (hc_nu1 c0 hc q'); simpl.
        exists (hc_nu1 c0 hc q'), c0, v, h0; simpl; split; intros; [|repeat eexists].
        apply sem_par_comm2.
        eapply sem_par_comm2; [apply H1|eassumption]. constructor. simpl. Focus 2. assumption.
        admit.
      - admit.
   - admit.
   - admit.
   * admit.
   + admit.
   *)
Qed.

(*
        exists (hc_nu1 c0 hc q'); simpl. 
        repeat eexists; intros; [|apply H1].
        constructor.
        simpl. admit.
        assumption.
        repeat eexists; intros; [|apply H1].
        repeat eexists; [| | reflexivity].
        simpl.
        subst; right; right; right; left. 
      simpl.
      simpl; exists (hc_nu1 c0 hc q'). simpl.
        apply H1.
        eassumption; try
        assumption.
        pc_atom.
        constructor; [assumption | apply H1].
      - subst; right; left.
        exists s'', h', ctx'.
        split; [assumption | reflexivity].
      - subst; right; right; left; repeat eexists; assumption.
      - subst; right; right; right; left. 
        exists (hc_nu2 c1 p0 hc'), b, v', h'. simpl.
        split; intros. constructor. simpl.
        admit. (* Name clash *)
        apply H1.
        repeat eexists; eassumption.
      - subst; right; right; right; right.
        exists (hc_nu2 c1 p0 hc'), b, v', h'. simpl.
        split; intros. constructor. simpl.
        admit. (* Name clash *)
        apply H1.
        repeat eexists; eassumption.
    Print hole_context.
      destruct IHsem_par_context1 as [[hc' [H1 H2]] | [[s' [h' [ctx' [H1 H2]]]] | 
      	[hc' [a [v' [h' [H1 [s' [h'' [ctx' [H2 [H3 H4]]]]]]]]]]]].
      - subst. admit.
      - admit.
      - admit.
    * admit.
  + admit.
  *)
Check has_ST.

  Lemma protocol_empty_MapsTo (P : protocol) c s 
    (H : MapsTo c s P) (Hempty : protocol_empty P) (Hineq : s <> st_end) : False.
  Proof.
    unfold protocol_empty in Hempty. rewrite for_all_iff in Hempty.
    specialize (Hempty _ _ H); destruct s; congruence.
    intros c1 c2 Hc st1 st2 Hst; subst; reflexivity.
  Qed.

Lemma compatible_step Pr n hc hc' p cs
  (Hcomp : compatible Pr (S n) hc p)
  (Hstep : forall pc, sem_par_context Pr cs (SpecLogic.hc_to_pc hc pc)
    l_tau (SpecLogic.hc_to_pc hc' pc)) :
  compatible Pr n hc' p.
Proof.
  intros pc m Hmn Hpc.
  unfold compatible in Hcomp.
  eapply Hcomp.
  destruct n.
  + assert (m = 0) by omega; subst; constructor.
  + assert (S m <= S (S n)) by omega; clear Hmn.
    specialize (Hcomp _ _ H Hpc).
  apply red_step; intros.
  unfold compatible in Hcomp.
  
  eapply Hcomp.
  Print compatible.
  unfold compatible in Hcomp.
  assert (m >= S n) as Hnm' by omega.
  specialize (Hcomp _ _ Hnm' Hpc).
  inversion Hcomp; subst. admit.
  eapply H0.
  apply Hstep.
  intros pc m Hmn Hpc.
  Print compatible.
  unfold compatible in Hcomp.
  assert (m <= S n) as Hnm' by omega.
  specialize (Hcomp _ _ Hnm' Hpc).
  inversion Hcomp; subst. admit.
  eapply H0.
  apply Hstep.
Qed.

    Lemma insert_context_comm hc1 hc2 pc : 
      SpecLogic.hc_to_pc (insert_context hc1 hc2) pc = SpecLogic.hc_to_pc hc1 (SpecLogic.hc_to_pc hc2 pc).
    Proof.
      induction hc1; simpl in *.
      + reflexivity.
      + rewrite IHhc1. reflexivity.
      + rewrite IHhc1. reflexivity.
    Qed.
    
    Lemma insert_context_comm2 hc1 hc2 pc : 
      SpecLogic.hc_to_pc (insert_context hc1 hc2) pc = SpecLogic.hc_to_pc hc1 (SpecLogic.hc_to_pc hc2 pc).
    Proof.
      induction hc1; simpl in *.
      + reflexivity.
      + rewrite IHhc1. reflexivity.
      + rewrite IHhc1. reflexivity.
    Qed.

  Lemma protocol_empty_add v st p (H : protocol_empty (add v st p)) 
  	(HIn : ~ In v p) : st = st_end /\ protocol_empty p.
  Proof.
    unfold protocol_empty in H.
    rewrite for_all_iff in H; [split|].
    + specialize (H v st).
      assert (MapsTo v st (add v st p)) as H1. {
        rewrite add_mapsto_iff; left; split; reflexivity.
      }
      specialize (H H1). destruct st; congruence.
    + intros. unfold protocol_empty.
      rewrite for_all_iff; intros c e H1.
      apply H with c. 
      assert (c = v \/ c <> v) by admit.
      destruct H0; subst.
      contradiction HIn.
      rewrite in_find_iff; intros H2.
      rewrite find_mapsto_iff in H1. rewrite H1 in H2; congruence.
      rewrite add_mapsto_iff. right. intuition congruence.
      intros st1 st2 Heq; subst. reflexivity.
    + intros c1 c2 Heq1 st1 st2 Heq2; subst. reflexivity.
  Qed.

  Lemma dual_end st (H : dual_ST st = st_end) : st = st_end.
  Proof.
    destruct st; simpl in *; subst; congruence.
  Qed.

  Lemma nil_inaction Pr cs p l p' (H : sem_par_context Pr cs p l p') (Hnil : pc_nil p) : False.
  Proof.
    generalize dependent cs; generalize dependent p'; generalize dependent l.
    induction p; simpl in *; intros.
    + destruct c; [inversion H|intuition].
    + destruct Hnil as [Hnilp Hnilq].
      inversion H; subst; firstorder.
  Qed.

  Lemma protocol_empty_tau Pr cs p l p' n P (H : sem_par_context Pr cs p l p')
    (H1 : STComp Pr (S n) P p) (Hempty : protocol_empty P) : l = l_tau.
  Proof.
    inversion H1; subst.
    + destruct (nil_inaction H H0).
    + specialize (H2 _ _ _ H).
      inversion H2; [reflexivity | |]; subst.
      * contradiction (protocol_empty_MapsTo H0 Hempty); intros; congruence.
      * contradiction (protocol_empty_MapsTo H0 Hempty); intros; congruence.
  Qed.

  Lemma STComp_dc Pr n m p pc (H : STComp Pr n p pc) (Hmn : m <= n) : STComp Pr m p pc.
  Proof.
    generalize dependent p; generalize dependent pc; generalize dependent n; induction m; intros.
    + constructor.
    + destruct n; [omega|]; inversion H; subst.
      * apply STComp_nil; assumption.
      * apply STComp_step; intros l pc' cs H2.
        specialize (H1 _ _ _ H2).
        inversion H1; subst.
        - apply STComp_tau. eapply IHm with n; [omega | assumption].
        - eapply STComp_send; try eassumption.
          eapply IHm with n; [omega | assumption].
        - eapply stComp_recv; intros; try eassumption.
          apply IHm with n; [omega|].
          apply H3; assumption.
  Qed.
  
  Lemma STComp_tau_step Pr n cs p pc pc' (H : STComp Pr (S n) p pc) 
    (Hstep : sem_par_context Pr cs pc l_tau pc') : STComp Pr n p pc'.
  Proof.
    inversion H; subst.
    + contradiction (nil_inaction Hstep H0).
    + specialize (H1 _ _ _ Hstep).
      inversion H1; subst; assumption.
  Qed.

  Lemma protocol_empty_rewrite p q (H : protocol_empty p) (Heq : p === q) : protocol_empty q.
  Proof.
    unfold protocol_empty in *; rewrite for_all_iff in *; intros.
    rewrite for_all_iff in H.
    rewrite <- Heq in H0.
    specialize (H k e H0). 
    apply H.
    intros ? ? ? ? ? ?; subst; reflexivity.
    intros ? ? ? ? ? ?; subst; reflexivity.
  Qed.

  Lemma add_commute (p : protocol) a b st1 st2 (H : a <> b) : 
  	add a st1 (add b st2 p) === add b st2 (add a st1 p).
  Proof.
    intros c.
    destruct (eq_dec a c).
    rewrite add_eq_o; [|assumption].
    destruct (eq_dec b c); [congruence|].
    rewrite add_neq_o; [|assumption].
    rewrite H0; rewrite add_eq_o; reflexivity.
    rewrite add_neq_o; [|assumption].
    destruct (eq_dec b c).
    rewrite add_eq_o; [|assumption].
    rewrite add_eq_o; [|assumption]. reflexivity.
    rewrite add_neq_o; [|assumption].
    rewrite add_neq_o; [|assumption].
    rewrite add_neq_o; [|assumption].
    reflexivity.
  Qed.
  
  Lemma add_overwrite (p : protocol) a st1 st2 :
  	add a st1 (add a st2 p) === add a st1 p.
  Proof.
    intros b.
    destruct (eq_dec a b).
    rewrite add_eq_o; [|assumption].
    rewrite add_eq_o; [|assumption].
    reflexivity.
    rewrite add_neq_o; [|assumption].
    rewrite add_neq_o; [|assumption].
    rewrite add_neq_o; [|assumption].
    reflexivity.
  Qed.
  
  Lemma STComp_rewrite_protocol Pr n p q pc
  	(H : STComp Pr n p pc) (Heq : p === q) : STComp Pr n q pc.
  Proof.
    generalize dependent pc; generalize dependent p; generalize dependent q;
    induction n; [constructor |]; intros.
    inversion H; subst.
    + apply STComp_nil; [assumption|].
      eapply protocol_empty_rewrite; eassumption.
    + apply STComp_step; intros l pc' cs H2.
      specialize (H1 _ _ _ H2).
      inversion H1; subst.
      - apply STComp_tau; eapply IHn; eassumption.
      - rewrite Heq in H0. 
        eapply STComp_send; try eassumption.
        eapply IHn; try eassumption.
        rewrite Heq. reflexivity.
      - rewrite Heq in H0.
        eapply stComp_recv; try eassumption; intros H4.
        eapply IHn; try eassumption; [|eapply H3; assumption].
        rewrite Heq; reflexivity.
  Qed.

  Lemma STComp_com Pr n v st (p : protocol) pc1 pc2
    (Hnotin : ~ In v p) 
    (H1 : STComp Pr n (add v (dual_ST st) p) pc1) 
    (H2 : STComp Pr n (add v st (empty ST)) pc2) :
    STComp Pr n p (pc_nu v pc1 pc2).
  Proof.
    generalize dependent st; generalize dependent p; generalize dependent pc1; generalize dependent pc2.
    induction n; [constructor|]; intros.
    inversion H1; subst.
    * apply protocol_empty_add in H0; [|assumption].
      destruct H0 as [H3 H4].
      assert (st = st_end) by (apply dual_end; assumption); subst; simpl in *.
      inversion H2; subst.
      + apply STComp_nil; simpl; [tauto|assumption].
      + apply STComp_step; intros.
        inversion H0; subst.
        - destruct (nil_inaction H13 H).
        - assert (l = l_tau). {
            eapply (protocol_empty_tau H13 H2); try eassumption.
            unfold protocol_empty. rewrite for_all_iff; intros; [|intros a b c d e f; subst; reflexivity].
            rewrite add_mapsto_iff in H6.
            destruct H6 as [[H6 H7] | [H6 H7]]; [subst; reflexivity|].
            rewrite empty_mapsto_iff in H7; destruct H7.
          }.
          subst; apply STComp_tau; eapply IHn with (st := st_end); simpl; [
            assumption |
            apply STComp_dc with (S n); [assumption | omega] |
            specialize (H5 _ _ _ H13); inversion H5; subst; apply H6
          ].
        - destruct (nil_inaction H12 H).
        - destruct (nil_inaction H12 H).
    * apply STComp_step; intros; inversion H; subst.
      + specialize (H0 _ _ _ H10); inversion H0; subst.
        - apply STComp_tau; eapply IHn; try eassumption.
          apply STComp_dc with (S n); [assumption | omega].
        - assert (c <> v) by (clear -H9; intro H; apply H9; subst; reflexivity); clear H9.
          rewrite add_mapsto_iff in H3.
          destruct H3 as [[Heq _] | [_ H3]]; [subst; congruence|].
          eapply STComp_send; try eassumption.
  		  eapply IHn with (st := st).   
 		  rewrite add_in_iff. intros [Heq | Hnotin']; [congruence | apply Hnotin; assumption].
 		  eapply STComp_rewrite_protocol; [eapply H5|].
 		  clear -H6.
 		  apply add_commute; assumption.
   		  eapply STComp_dc with (S n); [assumption | omega].
        - assert (c <> v) by (clear -H9; intro H; apply H9; subst; reflexivity); clear H9.
          rewrite add_mapsto_iff in H3.
  		  destruct H3 as [[Heq _] | [_ H3]]; [subst; congruence|].
 		  eapply stComp_recv; try eassumption.
 		  intros.
  		  apply IHn with (st := st).
 		  rewrite add_in_iff. intros [Heq | Hnotin']; [congruence | apply Hnotin; assumption].
  		  specialize (H4 H6).
  		  eapply STComp_rewrite_protocol; [eapply H4|].
  		  apply add_commute; assumption.
  		  apply STComp_dc with (S n); [assumption | omega].
      + clear H0; inversion H2; subst; [destruct (nil_inaction H10 H0)|].
        specialize (H3 _ _ _ H10); inversion H3; subst.
        - apply STComp_tau; apply IHn with (st := st); try assumption.
          apply STComp_dc with (S n); [assumption | omega].
        - assert (c <> v) by (clear -H9; intro H; apply H9; subst; reflexivity); clear H9.
          rewrite add_mapsto_iff in H0.
          destruct H0 as [[Heq _] | [_ H0]]; [subst; congruence|].
          rewrite empty_mapsto_iff in H0; destruct H0.
        - assert (c <> v) by (clear -H9; intro H; apply H9; subst; reflexivity); clear H9.
          rewrite add_mapsto_iff in H0.
  		  destruct H0 as [[Heq _] | [_ H0]]; [subst; congruence|].
  		  rewrite empty_mapsto_iff in H0; destruct H0.
      + apply STComp_tau.
        specialize (H0 _ _ _ H9).
        inversion H2; subst; [destruct (nil_inaction H10 H3)|].
        specialize (H4 _ _ _ H10); inversion H4; subst.
        inversion H0; subst.
        rewrite add_mapsto_iff in H12.
        destruct H12 as [[_ Heq] | [Hneq _]]; [|congruence]; subst. simpl in *.
        rewrite add_mapsto_iff in H11.
        destruct H11 as [[_ Heq] | [Hneq _]]; [|congruence]; inversion Heq; subst.
        specialize (H13 H15).
        eapply IHn with (st := st0); try assumption.
        eapply STComp_rewrite_protocol; [eapply H16 | apply add_overwrite].
        eapply STComp_rewrite_protocol; [eapply H13 | apply add_overwrite].
      + apply STComp_tau.
        specialize (H0 _ _ _ H9).
        inversion H2; subst; [destruct (nil_inaction H10 H3)|].
        specialize (H4 _ _ _ H10); inversion H4; subst.
        inversion H0; subst.
        rewrite add_mapsto_iff in H11.
        destruct H11 as [[_ Heq] | [Hneq _]]; [|congruence]; subst. simpl in *.
        rewrite add_mapsto_iff in H15.
        destruct H15 as [[_ Heq] | [Hneq _]]; [|congruence]; inversion Heq; subst.
        specialize (H16 H13).
        eapply IHn with (st := st0); try assumption.
        eapply STComp_rewrite_protocol; [eapply H16 | apply add_overwrite].
        eapply STComp_rewrite_protocol; [eapply H14 | apply add_overwrite].
  Qed.
  
  Lemma sem_par_context_start Pr cs p x y c p' (H : sem_par_context Pr cs p (l_start x y c) p') 
    : False.  
  Proof.
    remember (l_start x y c).
    induction H; inversion Heql; subst; tauto.
  Qed.

Lemma start_triple x y c P s p :
  st_safe y c s |-- (Forall v, ~In v p ->> (safe cc_skip (add v (dual_ST s) p) @ (P [{ (fun _ => vchan v) // x }]))) -->> safe (cc_start x y c) p @ P.
Proof.
  intros Pr k ctx T HT Pr' HPr n Hkn R HR Hsafe s' h Pr'' m hc HPR Hnm Hpr Hcomp.
  unfold spec_at in HT. simpl in HT.
  simpl. generalize dependent hc.
  induction m; [constructor|]; intros.
  apply red_step. intros.
  unfold safe in Hsafe; simpl in Hsafe.
  simpl in HT.
  apply hc_to_pc in H.
  destruct H as [[hc' [H1 H2]] | [pc'' [cs' [H1 H2]]]]; subst.
  + subst. apply IHm. omega.
    eapply compatible_step; try eassumption.
  + clear IHm.
    Transparent BILPre_Ops.
    Transparent SABIOps SABIOps2.
    simpl in HPR.
    destruct HPR as [h1 [h2 [Hh [HP HR']]]].
    unfold extSP in HR. destruct HR as [U [H2 H3]].
    inversion H1; subst; [|inversion H8].
    inversion H8; subst.
    generalize dependent (cs' ++ cs); clear cs cs'; intros cs Hcs Hsem.
    destruct cs; inversion Hcs; subst; clear Hcs.
    assert (n >= n) as Htemp by reflexivity.
    assert (Prog_sub Pr' Pr') as Htemp' by reflexivity.
    assert (~ In c p) as Htemp'' by admit.
    specialize (Hsafe _ _ Htemp' _ Htemp _ (extSP_refl R) Htemp'' (stack_add x (vchan c) s') h' Pr'' m
    	(insert_context hc (hc_nu1 c hc_hole (pc_atom (stack_add x0 (vchan c) (stack_empty var val)) (empty val)
    	  (cmd_to_context c'))))).
    simpl in Hsafe.
        
    progress rewrite insert_context_comm in Hsafe.
    apply Hsafe.
    do 3 eexists; [eassumption|].
    admit.
    omega.
    assumption.
    intros pc l Hlm Hcomp'.
    rewrite insert_context_comm. simpl.
    specialize (HT c Pr'' m (insert_context hc (hc_nu2 c pc hc_hole))). simpl in HT.
    rewrite insert_context_comm in HT. simpl in HT. apply HT.
    admit.
    omega.
    transitivity Pr'; assumption.
    intros a b d e.
    rewrite insert_context_comm. simpl.
    assert (compatible Pr m hc p) by admit.
    unfold compatible in H.
    assert (red Pr m (SpecLogic.hc_to_pc hc (pc_nu c pc a))).
    eapply H. reflexivity. clear H.
    unfold compatible in Hcomp.
    eapply STComp_com with s; try eassumption.
    
admit.  
admit.
  apply STComp_tau.
  apply IHn; try assumption.
  eapply STComp_tau_step.
    inversion H; subst.
  specialize (H12 _ _ H4).
  destruct H12 as [pc'' [H12 H13]].
  exists (pc_nu v pc'' pc2); split.
  apply sem_par_par1. simpl. clear -H3; intros H; apply H3; inversion H; reflexivity.
  apply H12.
  Print sem_par_context.
  SearchAbout In add.
  Lemma STComp_nu Pr n c st1 st2 p p1 p2 pc1 pc2 
    (H1 : STComp Pr n (add c st1 p1) pc1) (H2 : STComp Pr n (add c st2 p2) pc2) 
    (Hpartition : Partition p p1 p2) :
    STComp Pr n p (pc_nu c pc1 pc2).
  Proof.
    
  Qed.
  
  eapply STComp_nu; try eassumption.
  Focus 2. apply STComp_dc with (S n); [eassumption|omega].
  Check Partition.
  Print Partition.
  Print Disjoint.
    inversion H; subst.
    apply STComp_nil; assumption.
    
  inversion H10.
  inversion H10; subst.
  inversion H8. subst. simpl in *.
  apply STComp_tau.
      * specialize (IHp1 Hnilp _ _ H7).
    unfold pc_nil in Hnil.
      SearchAbout find MapsTo.
      Sea
      rewrite add_mapsto_iff.
Requre Import ExtLib.Tactics.
      apply H1.
      eapply H. rewrite add_mapsto_iff. right.
    setoid_rewrite add_mapsto_iff in H.
    SearchAbout MapsTo add.
    SearchAbout for_all.
    SearchAbout dict.
    induction p; simpl.
    induction p.
    apply STComp_step; intros l pc' H; inversion H; subst.
    + 
    Print STComp.
    inversion H9; subst.
    inversion H.
    remember (add v (dual_ST st) p) as p1.
    remember (add v st (empty ST)) as p2.
    generalize dependent st.
    induction H1; intros; simpl in *.
    + constructor.
    + assert (st = st_end) by admit; subst; simpl in *.
      remember (add v st_end (empty ST)) as p1.
      induction H2.
      * constructor.
      * apply STComp_nil; simpl; [tauto|]. admit.
      * admit.
    + apply STComp_step.
      intros.
      
Print STComp.    
    eapply STComp_tau. [|eapply IHSTComp; try eassumption].
      apply sem_par_par1; [simpl; intuition congruence|].
    eapply HT.
    simpl in HT.
    Check SpecLogic.hc_to_pc.
    Check red.
    Check red.
    apply HT.
    
    assert (red Pr'' m
          (pc_nu 0
             (SpecLogic.hc_to_pc hc (pc_atom (stack_add x (vchan 0) s') h' ctx'))
             (pc_atom (stack_add z (vchan 0) (stack_empty var val)) (empty val)
                (cmd_to_context c')))).
    apply Hsafe.
    admit.
    omega.
    assumption.
    simpl.
    unfold st in Hst.
    simpl.
    apply Hsafe.
Lemma send_triple (x y : var) (e : dexpr) st p P Q (v : channel) 
  (HPQ : P |-- Q) (Hembed : P |-- embed (open_eq x/V `(vchan v))) 
  (Hp : MapsTo v (st_send y Q st) p) :
  triple P p (cc_send x e) P (add v st p).
Proof.
  intros Pr k ctx T _ Pr' HPr n Hkn R HR Hsafe s h Pr'' m hc HPR Hnm Hpr Hcomp.
  generalize dependent hc.
  simpl. induction m; [constructor|]; intros.
  apply red_step; intros.
  

  apply hc_to_pc in H.
  destruct H as [[hc' [H1 H2]] | [[s' [h' [ctx' [H1 H2]]]] | 
  	[[hc' [a [v' [h' [H1 [s' [h'' [ctx' [H2 [H3 H4]]]]]]]]]] |
  	[hc' [a [v' [h' [H1 [s' [h'' [ctx' [H2 [H3 H4]]]]]]]]]]]]].
  + subst.
    eapply IHm.
    omega.
    admit.
  + subst.
    simpl in Hsafe.
    inversion H1; subst.
  + subst.
    inversion H2.
  + subst.
    inversion H2; subst.
    eapply Hsafe.
    admit.
    omega.
    assumption.
    eapply HPR.
    induction 
    simpl in H1.
  inversion H.

Lemma send_com Pr c hc s h x e ctx p pc 
  (H : sem_par_context Pr (pc_nu c (hc_to_pc hc (pc_atom s h (cc_send x e :: ctx))) p) l_tau pc) :
  (exists hc', pc = pc_nu c (hc_to_pc hc' (pc_atom s h (cc_send x e :: ctx))) p) \/
  (exists p',  pc = pc_nu c (hc_to_pc hc (pc_atom s h (cc_send x e :: ctx))) p') \/
  (exists hc', pc = pc_nu c (hc_to_pc hc' (pc_atom s h ctx)) p).
Proof.
  
  remember (pc_nu c (hc_to_pc hc (pc_atom s h (cc_send x e :: ctx))) p).
  induction H; try inversion Heqp0; subst.
  admit.
  right. left. eexists. reflexivity.
  
  generalize dependent pc. generalize dependent c. generalize dependent p.
  induction hc; intros; simpl in *. admit.
  inversion H; subst.
  
  specialize (IHhc _ _ _ H6).
  destruct IHhc as [[hc1 H1] | [[p'' H1] | [hc1 H1]]]; rewrite H1 in *.
  left. exists (hc_nu1 c hc1 p). reflexivity.
  right. left.
  eexists.
  rewrite H1. eexists. reflexivity.
  left. exists (hc_nu1 c hc1 p). reflexivity.
  left. exists (hc_nu1 c hc p). simpl.
  simpl in H5.
  specialize (IHhc _ _ _ H).
  eexists. rewrite H2. split.
  Focus 2.
  reflexivity.
  simpl.
  simpl
  remember (pc_nu c (hc_to_pc hc (pc_atom s h (cc_send x e :: ctx))) p).
  induction H; simpl in *; inversion Heqp0; subst.
  
  induction hc.
  simpl in *. 
  + admit.
  + simpl in H.
  + inversion H; subst.
    inversion H; subst. simpl in H5.
    Print sem_par_context.
    consider ((s x) ?[ eq ] c); intros.
    * admit.
    * simpl in Hcomp.
    intros.
    
  apply red_step. intros. simpl in H.
  simpl in Hsafe.
  
  hc_to_pc hc (pc_atom s h a) -l_tau-> pc ->
  (exists hc', pc = hc_to_pc hc' (pc_atom s h (cc_send x e :: ctx))) \/
  (exists hc', pc = hc_to_pc hc' (pc_atom s h ctx))
  
  admit. (* I believe you, but you need a lot of work *)
Qed.

Lemma start_triple p x c v P s :
	st v s c |-- triple P p (cc_start x c) P (add v (dual s) p).
Proof.
  intros Hst Pr k ctx T a Pr' HPr n Hkn R HR Hsafe s' h Pr'' m hc HPR Hnm Hpr Hcomp.
  simpl; destruct m; [constructor|].
  apply red_step. intros.
  
  
   simpl in H0.
  inversion H0; subst.
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