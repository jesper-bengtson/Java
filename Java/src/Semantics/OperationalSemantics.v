Require Import Program SepAlg SepAlgInsts Heap ProtocolLogic AssertionLogic SpecLogic SepAlgMap.
Require Import MapInterface MapFacts.
Require Import ILInsts ILogic ILEmbed ILEmbedTac ILQuantTac OpenILogic
               Open Subst Stack Lang SemCmd HeapArr Traces ST SemCmdRules BILogic.

Import SepAlgNotations.

Set Implicit Arguments.
Unset Strict Implicit.

Section Commands.

  Inductive assign_sem (x : var) (e : dexpr) : semCmdType :=
  | assign_ok : forall P PM s h t v
                       (He: eval e s = v),
      assign_sem x e P PM 1 s h t (Some (stack_add x v s, (h, t))).
  Program Definition assign_cmd x e := Build_semCmd (assign_sem x e) _ _.
  Next Obligation.
    intros H; inversion H.
  Qed.
  Next Obligation with eauto using assign_sem.
    unfold frame_property; intros.
    inversion HSem; subst; clear HSem; exists h...
  Qed.

  Inductive read_sem (x y : var) (f : field) : semCmdType :=
  | read_ok : forall ref v P PM (s : stack) (h : heap) (t : traces)
      (Rref  : s y = vptr ref)
      (Rmaps : MapsTo (ref,f) v (get_heap_ptr h)),
      read_sem x y f P PM 1 s h t (Some (stack_add x v s, (h, t)))
  | read_fail : forall ref P PM s (h : heap) (t : traces)
      (Sref   : s y = vptr ref)
      (Snotin : ~ In (ref,f) (get_heap_ptr h)),
      read_sem x y f P PM 1 s h t None.
  Program Definition read_cmd x y f := Build_semCmd (read_sem x y f) _ _.
  Next Obligation.
    intros H; inversion H.
  Qed.
  Next Obligation with eauto using read_sem.
    unfold frame_property; intros.
    inversion HSem; subst n s0 h0 s' big'; clear HSem; exists h; intuition.
    apply read_ok with ref; [assumption |]; specialize (HSafe _ (le_n _)).
    subst.
    apply isolate_heap_ptr in HFrame.
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
  Inductive read_arr_sem (x y : var) (path : list dexpr) : semCmdType :=
  | read_arr_ok P PM arr s h t v vpath
                (Sref : s y = varr arr)
                (Smap : List.map (fun e => eval e s) path = vpath)
(*                (Sarr : valid_path vpath)*)
                (Sfind : find_heap_arr arr (List.map val_to_nat vpath) (get_heap_arr h) = Some v) :
      read_arr_sem x y path P PM 1 s h t (Some (stack_add x v s, (h, t)))
  | read_arr_fail P PM arr s h t vpath
                  (Sref : s y = varr arr)
                  (Smap : List.map (fun e => eval e s) path = vpath)
                  (Sarr : ~ in_heap_arr arr (List.map val_to_nat vpath) (get_heap_arr h)) :
      read_arr_sem x y path P PM 1 s h t None.
  Program Definition read_arr_cmd x y path := Build_semCmd (read_arr_sem x y path) _ _.
  Next Obligation.
    intros H. inversion H.
  Qed.
  Next Obligation.
    unfold frame_property; intros; exists h.
    inversion HSem; subst; specialize (HSafe _ (le_n _)). 
    split; [assumption|].
    apply read_arr_ok with (arr := arr) (vpath := (List.map (fun e : dexpr => eval e s)) path);
      try assumption; try reflexivity.
    assert (in_heap_arr arr (List.map val_to_nat (List.map (fun e : dexpr => eval e s) path)) (get_heap_arr h)).
    apply dec_double_neg; [apply in_heap_arr_dec | intro H].
    apply HSafe.
    eapply read_arr_fail; try eassumption; try reflexivity.
    eapply find_heap_arr_frame; eauto. apply HFrame.
  Qed.

  Inductive write_arr_sem (x : var) (path : list dexpr) (e : dexpr) : semCmdType :=
  | write_arr_ok P PM arr s h ha' t vpath
                 (Sref : s x = varr arr)
                 (Smap : List.map (fun e' => eval e' s) path = vpath)
                 (Sin  : in_heap_arr arr (List.map val_to_nat vpath) (get_heap_arr h))
                 (Sha  : add_heap_arr arr (List.map val_to_nat vpath) (get_heap_arr h) (eval e s) = Some ha') :
      write_arr_sem x path e P PM 1 s h t (Some (s, ((mkheap (get_heap_ptr h) ha'), t)))
  | write_arr_fail P PM arr s h t vpath
                   (Sref : s x = varr arr)
                   (Smap : List.map (fun e' => eval e' s) path = vpath)
                   (Sin  : ~ in_heap_arr arr (List.map val_to_nat vpath) (get_heap_arr h)) :
      write_arr_sem x path e P PM 1 s h t None.
  Program Definition write_arr_cmd x path e := Build_semCmd (write_arr_sem x path e) _ _.
  Next Obligation.
    intros H. inversion H.
  Qed.
  Next Obligation.
    unfold frame_property; intros; inversion HSem; subst; clear HSem.
    specialize (HSafe _ (le_n _)).
    assert (in_heap_arr arr
          (List.map val_to_nat (List.map (fun e' : dexpr => eval e' s') path))
          (get_heap_arr h)). {
      apply dec_double_neg; [apply in_heap_arr_dec | intro H].
      apply HSafe; eapply write_arr_fail; try eassumption; reflexivity.
    }
    assert (sa_mul (get_heap_arr h) (get_heap_arr frame) (get_heap_arr big)) as HFrame_arr by (apply HFrame).
    destruct (add_heap_arr_frame _ _ _ _ _ _ _ HFrame_arr Sha H) as [ha'' [H1 H2]].
    exists (mkheap (get_heap_ptr h) ha'').
    split.
    apply split_heap; [ repeat rewrite remove_mkheap_ptr | repeat rewrite remove_mkheap_arr ].
    apply HFrame.
    apply H1.
    eapply write_arr_ok; try eassumption; reflexivity.
  Qed.

  Inductive alloc_arr_sem (x : var) (e : dexpr) : semCmdType :=
  | alloc_arr_ok (P : Prog_wf) PM (s s' : stack) (h : heap) (ha' : heap_arr) (t : traces) (n : nat)
                 (Sfresh_ha : forall i, ~ In (n, i) (get_heap_arr h)) 
                 (Sha : alloc_heap_arr n (val_to_nat (eval e s)) (get_heap_arr h) === ha') 
                 (Ss : s' = stack_add x (varr n) s) :
      alloc_arr_sem x e P PM 1 s h t (Some (s', ((mkheap (get_heap_ptr h) ha'), t))).
  Program Definition alloc_arr_cmd x e := Build_semCmd (alloc_arr_sem x e) _ _.
  Next Obligation.
    intros H; inversion H.
  Qed.
  Next Obligation.
    unfold frame_property; intros; inversion HSem; subst P n s s' big big'.
    specialize (HSafe _ (le_n _)).
    Lemma alloc_heap_arr_frame (n m : nat) (h frame h' h'' : heap_arr)
          (Hfresh : forall i, ~ In (n, i) frame)
          (Hh : alloc_heap_arr n m h === h')
          (HFrame : sa_mul h'' frame h) :
      exists h''', alloc_heap_arr n m h'' === h''' /\ sa_mul h''' frame h'.
    Proof.
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
    Qed.
    assert (sa_mul (get_heap_arr h) (get_heap_arr frame) (get_heap_arr h0)) as HFrame_arr by (apply HFrame).
    assert (forall i : nat, ~ In (n0, i) (get_heap_arr frame)) as Sfresh_frame. {
      intros i H; apply Sfresh_ha with i.
      apply sa_mulC in HFrame_arr; destruct (sa_mul_inL HFrame_arr H); assumption.
    }
    destruct (alloc_heap_arr_frame Sfresh_frame Sha HFrame_arr) as [ha'' [H1 H2]].
    exists (mkheap (get_heap_ptr h) ha''). split.
    apply split_heap; [ repeat rewrite remove_mkheap_ptr | repeat rewrite remove_mkheap_arr ].
    apply HFrame.
    apply H2.
    apply alloc_arr_ok with n0; try assumption.
    intros i H.
    specialize (Sfresh_ha i). apply Sfresh_ha.
    destruct (sa_mul_inL HFrame_arr H). assumption.
  Qed.
    
  Inductive alloc_sem (x : var) (C : class) : semCmdType :=
  | alloc_ok : forall (P : Prog_wf) PM (s s' : stack) (h : heap) (hp' : heap_ptr) t n fields
      (Snotnull : (n, C) <> pnull)
      (Sfresh_h : forall f, ~ In ((n, C), f) (get_heap_ptr h))
      (Sfields  : field_lookup P C fields)
      (Sh0      : sa_mul (get_heap_ptr h)
        (SS.fold (fun f h' => add ((n, C), f) (pnull : val) h') fields heap_ptr_unit) hp')
      (Ss0      : s' = stack_add x (vptr (n, C)) s),
      alloc_sem x C P PM 1 s h t (Some (s', ((mkheap hp' (get_heap_arr h)), t))).
  Program Definition alloc_cmd x C := Build_semCmd (alloc_sem x C) _ _.
  Next Obligation.
    intros H; inversion H.
  Qed.
  Next Obligation.
    unfold frame_property; intros.
    inversion HSem; subst; clear HSem.
    assert (sa_mul (get_heap_ptr h) (get_heap_ptr frame) (get_heap_ptr big)) as HFrame_ptr by (apply HFrame).
    destruct (sa_mulA HFrame_ptr Sh0) as [h5 [H1 H2]].
    apply sa_mulC in H2; destruct (sa_mulA H1 H2) as [h6 [H3 H5]].
    exists (mkheap h6 (get_heap_arr h)).
    split.
    apply split_heap; [ repeat rewrite remove_mkheap_ptr | repeat rewrite remove_mkheap_arr ].
    apply sa_mulC; apply H5.
    apply HFrame.
    eapply alloc_ok; [eassumption | | eassumption | apply sa_mulC; assumption | reflexivity].
    intros f H6; apply (Sfresh_h f).
    apply sa_mulC in H2.
    destruct (sa_mul_inL H2 H6) as [H8 H9].    
    destruct (sa_mul_inR Sh0 H9) as [[H10 H11] | [H10 H11]]; [assumption|].
    apply sa_mulC in H1; destruct (sa_mul_inL H1 H10); intuition.
  Qed.

  Inductive write_sem (x:var) (f:field) (e:dexpr) : semCmdType := 
  | write_ok : forall P PM (s: stack) (h : heap) (hp' : heap_ptr) t ref v
      (Sref: s x = vptr ref)
      (Sin:  In (ref,f) (get_heap_ptr h) )
      (Heval : eval e s = v)
      (Sadd: hp' = add (ref,f) v (get_heap_ptr h) ),
      write_sem x f e P PM 1 s h t (Some (s, ((mkheap hp' (get_heap_arr h)), t)))
  | write_fail : forall P PM (s: stack) h t ref
      (Sref:   s x = vptr ref)
      (Sin : ~ In (ref, f) (get_heap_ptr h)),
      write_sem x f e P PM 1 s h t None.
  Program Definition write_cmd x f e := Build_semCmd (write_sem x f e) _ _.
  Next Obligation.
    intros H; inversion H.
  Qed.
  Next Obligation.
    unfold frame_property; intros.
    inversion HSem. subst; clear HSem.
    assert (sa_mul (get_heap_ptr h) (get_heap_ptr frame) (get_heap_ptr big)) as HFrame_ptr by (apply HFrame).
    assert (~ In (ref, f) (get_heap_ptr frame)). {
	    intros H. 
    	apply (HSafe 1); [omega |].
    	eapply write_fail; [eassumption|].
    	destruct (sa_mul_inR HFrame_ptr Sin); intuition.
    }
    exists (mkheap (add (ref, f) (eval e s') (get_heap_ptr h)) (get_heap_arr h)). split.
    apply split_heap; [ repeat rewrite remove_mkheap_ptr | repeat rewrite remove_mkheap_arr ].
    apply sa_mul_add; assumption. apply HFrame.
    eapply write_ok; try eassumption; try reflexivity.
    destruct (sa_mul_inR HFrame_ptr Sin); intuition.
  Qed.

  Inductive send_sem (x v : var) : semCmdType :=
  | send_ok : forall P PM (s: stack) (h mres: heap) (t t': traces) (tr: trace) (c: stptr)
    (Sref: s x = vst c)
    (Strace: MapsTo c (tsend (s v) mres tr) t)
    (Smarshall: marshall (s v) h mres)
    (Sadd: t' = add c tr t),
    send_sem x v P PM 1 s h t (Some (s, (h, t')))
  | send_fail2 : forall P PM (s: stack) (h mres: heap) (t: traces) (tr: trace) (c: stptr)
  	(Sref: s x = vst c)
    (Strace: MapsTo c (tsend (s v) mres tr) t)
    (Smarshalls: ~ marshall (s v) h mres),
    (* Unable to marshall the value pointed to by (s v) in the heap h *)
    send_sem x v P PM 1 s h t None
  .  
  Program Definition send_cmd x v := Build_semCmd (send_sem x v) _ _.
  Next Obligation.
    intros H; inversion H.
  Qed.
  Next Obligation.
    unfold frame_property; intros.
    inversion HSem. subst; clear HSem.
    exists h; split; [assumption |]. 
    assert (DisjointHeaps frame mres \/ ~DisjointHeaps frame mres) by admit (* fangel *).
    destruct H.
    * eapply send_ok; [ apply Sref | apply Strace | | reflexivity].
      eapply marshall_into_smaller in H; [| apply HFrame | apply Smarshall].
      destruct H; [eapply H | eapply marshall_into_unit; [ apply H | apply Smarshall]].
    * eapply marshall_fails_outside in H; [| apply HFrame | apply Smarshall].
      destruct H.
      + exfalso.
        apply (HSafe 1); [omega|].
        eapply send_fail2; [apply Sref | apply Strace | apply H].
      + eapply send_ok; [apply Sref | apply Strace | | reflexivity].
        eapply marshall_into_unit; [ apply H | apply Smarshall].
  Qed.

  Inductive recv_sem (v x : var) : semCmdType :=
  | recv_ok : forall P PM (s: stack) (h rh h': heap) (t t': traces) (tr: trace) (c: stptr) (rv : sval)
    (Sref: s x = vst c)
    (Strace: MapsTo c (trecv rv rh tr) t)
    (Snewheap : sa_mul h rh h')
    (Sadd: t' = add c tr t),
    recv_sem v x P PM 1 s h t (Some (stack_add v rv s, (h', t')))
  .
  Program Definition recv_cmd v x := Build_semCmd (recv_sem v x) _ _.
  Next Obligation.
    intros H; inversion H.
  Qed.
  Next Obligation.
    unfold frame_property; intros.
    inversion HSem. subst; clear HSem.
    remember (mkheap (update (elt:=val) (get_heap_ptr h) (get_heap_ptr rh))
           (update (elt:=val) (get_heap_arr h) (get_heap_arr rh))) as h'.
    exists h'. split.
    * apply sa_mulC in HFrame.
      eapply sa_mulA in Snewheap; [| apply HFrame].
      destruct Snewheap as [h'0 [H0 Snewheap]].
      destruct (heap_eq_dec h'0 h') as [Heq | Hneq].
      + apply sa_mulC in Snewheap.
        eapply sa_mul_mon. apply Heq. apply Snewheap.
      + assert (h'0 === mkheap (update (elt:=val) (get_heap_ptr h) (get_heap_ptr rh))
                               (update (elt:=val) (get_heap_arr h) (get_heap_arr rh))). {
          eapply sa_mul_heapResEq. apply H0.
          apply DisjointHeaps_sa_mul. eapply sa_mul_DisjointHeaps. apply H0.
        }
        rewrite <- Heqh' in H.
        exfalso. apply Hneq. apply H.
     * eapply recv_ok; [apply Sref | apply Strace | | reflexivity].
       rewrite Heqh'. apply DisjointHeaps_sa_mul.
       apply sa_mulC in HFrame.
       eapply sa_mulA in Snewheap; [| apply HFrame].
       destruct Snewheap as [h'0 [H0 _]].
       apply sa_mul_DisjointHeaps in H0.
       apply H0.
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
  | call_failS : forall (P : Prog_wf) PM s h t
      (HLFail  : forall mrec, ~ method_lookup P (C s) m mrec),
      call_sem rvar C m es c sc P PM 1 s h t None
  | call_failC : forall (P : Prog_wf) PM ps rexpr (s : stack) h t n
      (HLookup : method_lookup P (C s) m (Build_Method ps c rexpr))
      (HLen    : length ps = length es)
      (HFail   : sc P PM n (create_stack ps (eval_exprs s es)) h t None),
      call_sem rvar C m es c sc P PM (S n) s h t None
  | call_failL : forall (P : Prog_wf) PM ps rexpr s h t
      (HLookup : method_lookup P (C s) m (Build_Method ps c rexpr))
      (HLen    : length ps <> length es),
      call_sem rvar C m es c sc P PM 1 s h t None
  | call_ok    : forall (P : Prog_wf) PM ps rexpr (s sr : stack) (h hr : heap) (t tr : traces) n
      (HLookup : method_lookup P (C s) m (Build_Method ps c rexpr))
      (HLen    : length ps = length es)
      (HSem    : sc P PM n (create_stack ps (eval_exprs s es)) h t (Some (sr, (hr, tr)))),
      call_sem rvar C m es c sc P PM (S n) s h t
        (Some (stack_add rvar (eval rexpr sr) s, (hr, tr))).
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
  
  Inductive start_sem (C : class) (m : method) (x : var) (p : protocol) (c : cmd) (sc : semCmd)
    : semCmdType :=
  | start_failM   : forall (P : Prog_wf) PM (a : var) (chan : stptr) (s: stack) (h : heap) (trs : traces) (tr : trace) (rexpr : dexpr) n
       (HProtocol : (forall T, MapsTo p T PM -> ST_trace_strong P (T s) tr))
       (HFresh    : ~ In chan trs)
       (HLookup   : method_lookup P C m (Build_Method (a::nil) c rexpr))
       (HSem      : sc P PM n (stack_add a (vst chan) (stack_empty _)) heap_unit (add chan tr (empty _)) None),
       start_sem C m x p c sc P PM (S n) s h trs None
  | start_failE   : forall (P : Prog_wf) PM (a : var) (chan : stptr) (s rs: stack) (h rh : heap) (trs rtrs : traces) (tr : trace) (rexpr : dexpr) n
      (HProtocol : (forall T, MapsTo p T PM -> ST_trace_strong P (T s) tr)) 
       (HFresh    : ~ In chan trs)
       (HLookup   : method_lookup P C m (Build_Method (a::nil) c rexpr))
       (HSem      : sc P PM n (stack_add a (vst chan) (stack_empty _)) heap_unit (add chan tr (empty _)) (Some (rs, (rh, rtrs))))
       (HOngoing  : exists oc otr, MapsTo oc otr rtrs /\ otr <> tinit),
       start_sem C m x p c sc P PM (S n) s h trs None
  | start_ok      : forall (P : Prog_wf) PM (a : var) (chan : stptr) (s rs: stack) (h rh : heap) (trs : traces) (tr : trace) (rexpr : dexpr) n
       (HProtocol : (forall T, MapsTo p T PM -> ST_trace_strong P (T s) tr)) 
       (HFresh    : ~ In chan trs)
       (HLookup   : method_lookup P C m (Build_Method (a::nil) c rexpr))
       (HSem      : sc P PM n (stack_add a (vst chan) (stack_empty _)) heap_unit (add chan tr (empty _)) (Some (rs, (rh, (add chan tinit (empty _)))))),
       start_sem C m x p c sc P PM (S n) s h trs (Some ((stack_add x (vst chan) s), (h, (add chan (dual tr) trs)))).
  Program Definition start_cmd C m x p c sc := Build_semCmd (start_sem C m x p c sc) _ _.
  Next Obligation.
    intros H; inversion H.
  Qed.
  Next Obligation with eauto using start_sem.
    unfold frame_property; intros.
    inversion HSem; subst; clear HSem.
    exists h.
    split; [assumption |].
    eapply start_ok; eassumption.
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
      semantics (cassert e) (assert_cmd (vlogic_eval e))
  | semsend : forall x y,
      semantics (csend x y) (send_cmd x y)
  | semrecv : forall v x,
      semantics (crecv v x) (recv_cmd v x)
  | semstart : forall (x : var) (C : class) m (p : protocol) c sc
      (HSem  : semantics c sc),
      semantics (cstart x C m p) (start_cmd C m x p c sc)
  .

  Definition c_not_modifies c x :=
    forall sc, semantics c sc -> not_modifies sc x.

  Lemma modifies_syn_sem c x :
     ~ SS.In x (modifies c) -> c_not_modifies c x.
  Proof.
    induction c; simpl in *; intros HNM; intros sc HSem; inversion_clear HSem.
    + rewrite SS'.singleton_iff in HNM; intros P PM s s0 h h0 t t0 n HAsgn;
      simpl in *; inversion HAsgn; subst.
      rewrite stack_lookup_add2; trivial.
    + intros P PM s s0 h h0 t t0 n HSkip; simpl in *; inversion HSkip; subst; trivial.
    + intros P PM s s0 h h0 t t0 n HSeq; simpl in *; inversion HSeq; subst.
      transitivity (s2 x).
      * eapply IHc1; [| eassumption | eassumption]; intros HIn; apply HNM;
        rewrite SS'.union_iff; auto.
      * eapply IHc2; [| eassumption | eassumption]; intros HIn; apply HNM;
        rewrite SS'.union_iff; auto.
    + intros P PM s s0 h h0 t t0 n HND; simpl in *; inversion HND; subst; clear HND.
      * inversion H6; subst.
        apply assume_inv in H8; destruct H8; subst.
        eapply IHc1; [| eassumption | eassumption]; intros HIn; apply HNM;
          rewrite SS'.union_iff; auto.
      * inversion H6; subst.
        apply assume_inv in H8; destruct H8; subst.
        eapply IHc2; [| eassumption | eassumption]; intros HIn; apply HNM;
        rewrite SS'.union_iff; auto.
    + intros P PM s s0 h h0 t t0 n HKl; simpl in *; inversion HKl; subst; clear HKl.
      apply assume_inv in H9; destruct H9; destruct H0; subst; simpl in *.
      remember (Some (s0, (h0, t0))); induction H7; subst;
        [inversion Heqo; trivial | discriminate | discriminate |].
      transitivity (s1 x); simpl in *.
      * inversion H; subst; clear H.
        apply assume_inv in H9; destruct H9; subst.
        eapply IHc; eassumption.
      * apply IHkleene_sem; assumption.
    + intros P PM s s0 h h0 t t0 n HWr; simpl in *; inversion HWr; subst; reflexivity.
    + rewrite SS'.singleton_iff in HNM; intros P PM s s0 h h0 t t0 n HRd; simpl in *;
      inversion HRd; subst; rewrite stack_lookup_add2; trivial.
    + rewrite SS'.singleton_iff in HNM; intros P PM s s0 h h0 t t0 n Hrd; simpl in *.
      inversion Hrd; subst. rewrite stack_lookup_add2; [reflexivity | assumption].
    + intros P PM s s0 h h0 t t0 n Hrd; simpl in *; inversion Hrd; reflexivity.
    + rewrite SS'.singleton_iff in HNM; intros P PM s s0 h h0 t t0 n Hrd; simpl in *.
      inversion Hrd; subst. rewrite stack_lookup_add2; [reflexivity | assumption].
    + rewrite SS'.singleton_iff in HNM; intros P PM s s0 h h0 t t0 n HCl; simpl in *;
      inversion HCl; subst; rewrite stack_lookup_add2; trivial.
    + rewrite SS'.singleton_iff in HNM; intros P PM s s0 h h0 t t0 n HCl; simpl in *;
      inversion HCl; subst; rewrite stack_lookup_add2; trivial.
    + rewrite SS'.singleton_iff in HNM; intros P PM s s0 h h0 t t0 n HCl; simpl in *;
      inversion HCl; subst; rewrite stack_lookup_add2; trivial.
    + intros P PM s s0 h h0 t t0 n HAs; inversion HAs; subst; reflexivity.
    + intros P PM s s0 h h0 t t0 n HAs; inversion HAs; subst; reflexivity.
    + rewrite SS'.singleton_iff in HNM; intros P PM s s0 h h0 t t0 n HCl; simpl in *;
      inversion HCl; subst; rewrite stack_lookup_add2; trivial.
    + rewrite SS'.singleton_iff in HNM; intros P PM s s0 h h0 t t0 n HCl; simpl in *;
      inversion HCl; subst; rewrite stack_lookup_add2; trivial.
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

  Definition triple (P Q : psasn) (c : cmd) :=
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

  Definition method_spec C m (ps : list var) (rn : var) (P Q : psasn) := (
    NoDup (rn :: ps) /\\
    Exists ps' : (list var), Exists c : cmd, Exists re : dexpr,
      [prog] (fun X : Prog_wf => method_lookup X C m (Build_Method ps' c re)
        /\ length ps = length ps' /\
        (forall x, List.In x ps' -> ~ SS.In x (modifies c)))
      //\\ {[ psasn_subst P (substl_trunc_aux (zip ps (List.map var_expr ps'))) ]}
         c {[ psasn_subst Q (substl_trunc_aux (zip (rn :: ps) (eval re :: (List.map var_expr ps'))))]}
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
    admit (* jesper *).
(*    setoid_rewrite HP. setoid_rewrite HQ. reflexivity.*)
  Qed.

  Add Parametric Morphism : method_spec with signature
    eq ==> eq ==> eq ==> eq ==>
      lequiv ==> lequiv ==> lequiv
    as method_spec_bientails_m.
  Proof.
    split; apply method_spec_entails_m; try rewrite ?H, ?H0; reflexivity.
  Qed.


  Lemma c_triple_zero P (p q : psasn) (c : cmd) :
    ({[ p ]} c {[ q ]}) P 0.
  Proof.
    intros sc n Hn Q HPQ sem R PM k m s h t HQR Hk Hv Hp.
    assert (m = 0) by omega.
    assert (k = 0) by omega.
    subst. split.
    + apply safe_zero.
    + intros t' h' s'' Hc. apply cmd_zero in Hc. contradiction.
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

  Lemma triple_false (G : spec) (Q : psasn) c :
    G |-- {[lfalse]} c {[Q]}.
  Proof.
    intros n; simpl in *; intros; destruct H4.
  Qed.

  Lemma roc (P P' Q Q' : psasn) c (G : spec)
    (HPre  : P  |-- P')
    (HPost : Q' |-- Q)
    (Hc    : G  |-- {[P']} c {[Q']}) :
    G |-- {[P]} c {[Q]}.
  Proof.  
    rewrite Hc.
    unfold triple. lforallR sc. apply lpropimplR; intros Hsc.
    lforallL sc. apply lpropimplL; [assumption|]. apply rule_of_consequence; assumption.
  Qed.

  Lemma roc_pre (P P' Q : psasn) c G
    (HPre : P |-- P')
    (Hc   : G |-- {[P']} c {[Q]}) :
    G |-- {[P]} c {[Q]}.
  Proof.
  	eapply roc; eassumption || reflexivity.
  Qed.

  Lemma roc_post (P Q Q' : psasn) c G
    (Hc : G  |-- {[P]} c {[Q']})
    (HPost : Q' |-- Q) :
    G |-- {[P]} c {[Q]}.
  Proof.
    eapply roc; eassumption || reflexivity.
  Qed.
  
  Lemma rule_frame_ax_list (P Q : psasn) (R : sasn) c (xs: list var)
    (HMod : forall x, ~ List.In x xs -> c_not_modifies c x) :
    {[ P ]} c {[ Q ]} |--
    {[ P ** embed R ]} c {[ Q ** Exists vs, embed (apply_subst R (subst_fresh vs xs)) ]}.
  Proof.
    unfold triple. lforallR sc; apply lpropimplR; intro Hsc. lforallL sc. 
    apply lpropimplL; [assumption|].
    apply frame_rule. unfold c_not_modifies in HMod. intros. apply HMod; auto.
  Qed.

  Definition subst_mod_asn (R: sasn) (c: cmd) : sasn :=
    Exists vs, apply_subst R (subst_fresh vs (SS.elements (modifies c))).

  Lemma rule_frame_ax (P Q : psasn) (R : sasn) c : 
    {[ P ]} c {[ Q ]} |--
    {[ P ** embed R ]} c {[ Q ** embed (subst_mod_asn R c) ]}.
  Proof.
    apply rule_frame_ax_list. intros x HnotIn. apply modifies_syn_sem.
    rewrite SS'.In_elements_iff. assumption.
  Qed.

  Lemma rule_frame (P Q : psasn) (R : sasn) c G 
    (HPre : G |-- {[P]} c {[Q]}) :
    G |-- {[ P ** embed R ]} c {[ Q ** embed (subst_mod_asn R c) ]}.
  Proof.
    intros; rewrite <- rule_frame_ax; assumption.
  Qed.
  Implicit Arguments rule_frame [[P] [Q] [R] [c] [G]].

  Lemma exists_into_precond2 {A} (P: A -> psasn) c q :
    (Forall x, {[P x]} c {[q]}) -|- {[Exists x, P x]} c {[q]}.
  Proof.
    unfold triple; setoid_rewrite <- exists_into_precond; split.
    + lforallR sc. apply lpropimplR; intro Hsc; lforallR x.
      lforallL x sc. apply lpropimplL; [assumption | reflexivity].
    + lforallR x sc. apply lpropimplR; intro Hsc.
      lforallL sc. apply lpropimplL; [assumption | lforallL x; reflexivity].
  Qed.
  
  (* fangel, psasn 
  Lemma existentialise_triple (x : var) (P Q : sasn) c (G : spec) 
	(H : forall (v : val), G |-- {[@lembedand vlogic sasn _ _ (open_eq (x/V) (`v)) P]} c {[Q]}) :
    G |-- {[P]} c {[Q]}.
  Proof.
    eapply roc_pre; [apply existentialise_var with (x0 := x)|].
    rewrite <- exists_into_precond2. lforallR y. apply H.
  Qed.
  *)

End StructuralRules.