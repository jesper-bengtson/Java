Require Import Program SepAlg SepAlgInsts Heap ProtocolLogic AssertionLogic SpecLogic SepAlgMap.
Require Import MapInterface MapFacts.
Require Import ILInsts ILogic ILEmbed ILEmbedTac ILQuantTac OpenILogic
               Open Subst Stack Lang SemCmd HeapArr Traces ST SemCmdRules BILogic Util.

Import SepAlgNotations.

Set Implicit Arguments.
Unset Strict Implicit.

Section Commands.

  Inductive assign_sem (x : var) (e : dexpr) : semCmdType :=
  | assign_ok : forall P s h cl v
                       (He: eval e s = v),
      assign_sem x e P s h cl (t_tau (stack_add x v s) h cl t_end).
  Program Definition assign_cmd x e := Build_semCmd (assign_sem x e) _ _.
  Next Obligation.
    intros H; inversion H.
  Qed.
  Next Obligation with eauto using assign_sem, frame_trace.
    unfold frame_property; intros.
    inversion HSem; subst; clear HSem. exists (t_tau (stack_add x (eval e s) s) h cl t_end)...
  Qed.

  Inductive read_sem (x y : var) (f : field) : semCmdType :=
  | read_ok : forall ref v P (s : stack) (h : heap) cl
      (Rref  : s y = vptr ref)
      (Rmaps : MapsTo (ref,f) v h),
      read_sem x y f P s h cl (t_tau (stack_add x v s) h cl t_end)
  | read_fail : forall ref P s (h : heap) cl
      (Sref   : s y = vptr ref)
      (Snotin : ~ In (ref,f) h),
      read_sem x y f P s h cl t_fail.
  Program Definition read_cmd x y f := Build_semCmd (read_sem x y f) _ _.
  Next Obligation.
    intros H; inversion H.
  Qed.
  Next Obligation with eauto using read_sem, frame_trace.
    unfold frame_property; intros.
    inversion HSem; subst; clear HSem.
    destruct (sa_mul_mapstoRT HFrame Rmaps) as [[H1 H2] | [H1 H2]].
    exists (t_tau (stack_add x v s) h cl t_end)...
    exists t_fail...
    exists t_fail...
    split; [constructor|].
    apply read_fail with ref; [assumption|].
    intros H; apply Snotin.
    destruct (sa_mul_inL HFrame H); assumption.
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
(*
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


  Require Import ZArith.
  Definition valid_path (vpath : list val) := 
    List.Forall (fun v => exists a, v = vint a /\ (a >= 0)%Z) vpath.

  Inductive read_arr_sem (x y : var) (path : list dexpr) : semCmdType :=
  | read_arr_ok P PM arr s h STs v vpath
                (Sref : s y = varr arr)
                (Smap : List.map (fun e => eval e s) path = vpath)
(*                (Sarr : valid_path vpath)*)
                (Sfind : find_heap_arr arr (List.map val_to_nat vpath) (get_heap_arr h) = Some v) :
      read_arr_sem x y path P PM 1 s h STs (Some (stack_add x v s, (h, STs)))
  | read_arr_fail P PM arr s h STs vpath
                  (Sref : s y = varr arr)
                  (Smap : List.map (fun e => eval e s) path = vpath)
                  (Sarr : ~ in_heap_arr arr (List.map val_to_nat vpath) (get_heap_arr h)) :
      read_arr_sem x y path P PM 1 s h STs None.
  Program Definition read_arr_cmd x y path := Build_semCmd (read_arr_sem x y path) _ _.
  Next Obligation.
    intros H. inversion H.
  Qed.
  Next Obligation.
    unfold frame_property; intros; exists h; exists T.
    inversion HSem; subst; specialize (HSafe _ (le_n _)); intuition.
    apply read_arr_ok with (arr := arr) (vpath := (List.map (fun e : dexpr => eval e s)) path);
      try assumption; try reflexivity.
    assert (in_heap_arr arr (List.map val_to_nat (List.map (fun e : dexpr => eval e s) path)) (get_heap_arr h)).
    apply dec_double_neg; [apply in_heap_arr_dec | intro H].
    apply HSafe.
    eapply read_arr_fail; try eassumption; try reflexivity.
    eapply find_heap_arr_frame; eauto. apply HFrame.
  Qed.

  Inductive write_arr_sem (x : var) (path : list dexpr) (e : dexpr) : semCmdType :=
  | write_arr_ok P PM arr s h ha' STs vpath
                 (Sref : s x = varr arr)
                 (Smap : List.map (fun e' => eval e' s) path = vpath)
                 (Sin  : in_heap_arr arr (List.map val_to_nat vpath) (get_heap_arr h))
                 (Sha  : add_heap_arr arr (List.map val_to_nat vpath) (get_heap_arr h) (eval e s) = Some ha') :
      write_arr_sem x path e P PM 1 s h STs (Some (s, ((mkheap (get_heap_ptr h) ha'), STs)))
  | write_arr_fail P PM arr s h STs vpath
                   (Sref : s x = varr arr)
                   (Smap : List.map (fun e' => eval e' s) path = vpath)
                   (Sin  : ~ in_heap_arr arr (List.map val_to_nat vpath) (get_heap_arr h)) :
      write_arr_sem x path e P PM 1 s h STs None.
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
    exists (mkheap (get_heap_ptr h) ha''). exists T.
    split.
    apply split_heap; [ repeat rewrite remove_mkheap_ptr | repeat rewrite remove_mkheap_arr ].
    apply HFrame.
    apply H1.
    split; [assumption |].
    eapply write_arr_ok; try eassumption; reflexivity.
  Qed.

  Inductive alloc_arr_sem (x : var) (e : dexpr) : semCmdType :=
  | alloc_arr_ok (P : Prog_wf) PM (s s' : stack) (h : heap) (ha' : heap_arr) (STs : STs) (n : nat)
                 (Sfresh_ha : forall i, ~ In (n, i) (get_heap_arr h)) 
                 (Sha : alloc_heap_arr n (val_to_nat (eval e s)) (get_heap_arr h) === ha') 
                 (Ss : s' = stack_add x (varr n) s) :
      alloc_arr_sem x e P PM 1 s h STs (Some (s', ((mkheap (get_heap_ptr h) ha'), STs))).
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
    exists (mkheap (get_heap_ptr h) ha''). exists T. split.
    apply split_heap; [ repeat rewrite remove_mkheap_ptr | repeat rewrite remove_mkheap_arr ].
    apply HFrame.
    apply H2.
    split; [subst bigT'; assumption |].
    apply alloc_arr_ok with n0; try assumption.
    intros i H.
    specialize (Sfresh_ha i). apply Sfresh_ha.
    destruct (sa_mul_inL HFrame_arr H). assumption.
  Qed.
  *)
  
  Inductive alloc_sem (x : var) (C : class) : semCmdType :=
  | alloc_ok : forall (P : Prog_wf) (s s' : stack) (h : heap) (hp' : heap) n fields cl
      (Snotnull : (n, C) <> pnull)
      (Sfresh_h : forall f, ~ In ((n, C), f) h)
      (Sfields  : field_lookup P C fields)
      (Sh0      : sa_mul h
        (SS.fold (fun f h' => add ((n, C), f) (pnull : val) h') fields heap_unit) hp')
      (Ss0      : s' = stack_add x (vptr (n, C)) s),
      alloc_sem x C P s h cl (t_tau s' hp' cl t_end).
  Program Definition alloc_cmd x C := Build_semCmd (alloc_sem x C) _ _.
  Next Obligation.
    intros H; inversion H.
  Qed.
  Next Obligation.
    unfold frame_property; intros.
    inversion HSem; subst; clear HSem.
    exists (t_tau (stack_add x (n, C0 s)
    destruct (sa_mulA HFrame Sh0) as [h5 [H1 H2]].
    apply sa_mulC in H2; destruct (sa_mulA H1 H2) as [h6 [H3 H5]].
    exists h6.
    split.
    apply sa_mulC; apply H5.
    eapply alloc_ok; [eassumption | | eassumption | apply sa_mulC; assumption | reflexivity].
    intros f H6; apply (Sfresh_h f).
    apply sa_mulC in H2.
    destruct (sa_mul_inL H2 H6) as [H8 H9].    
    destruct (sa_mul_inR Sh0 H9) as [[H10 H11] | [H10 H11]]; [assumption|].
    apply sa_mulC in H1; destruct (sa_mul_inL H1 H10); intuition.
  Qed.
*)

  Inductive write_sem (x:var) (f:field) (e:dexpr) : semCmdType := 
  | write_ok : forall P (s: stack) (h : heap) (hp' : heap) ref v cl
      (Sref: s x = vptr ref)
      (Sin:  In (ref,f) h )
      (Heval : eval e s = v)
      (Sadd: hp' = add (ref,f) v h ),
      write_sem x f e P s h cl (t_tau s hp' cl t_end)
  | write_fail : forall P (s: stack) h ref cl
      (Sref:   s x = vptr ref)
      (Sin : ~ In (ref, f) h),
      write_sem x f e P s h cl t_fail.
  Program Definition write_cmd x f e := Build_semCmd (write_sem x f e) _.
  Next Obligation.
    intros H; inversion H.
  Qed.
(*
  Next Obligation.
    unfold frame_property; intros.
    inversion HSem. subst; clear HSem.
    assert (~ In (ref, f) frame). {
	    intros H. 
	    eapply HSafe; [reflexivity | apply trace_appendEndR |].
    	eapply write_fail; [eassumption|].
    	destruct (sa_mul_inR HFrame Sin); intuition.
    }
    exists (add (ref, f) (eval e s') h). split.
    apply sa_mul_add; assumption. 
    eapply write_ok; try eassumption; try reflexivity.
    destruct (sa_mul_inR HFrame Sin); intuition.
  Qed.
*)
  Require Import Util Marshal.
  Inductive send_sem (x v : var) : semCmdType :=
  | send_ok     : forall Pr (s: stack) (h mh: heap) (c: stptr) cl
    (Sref       : s x = vst c)
    (Smarshal   : Marshal Pr (s v) h mh),
    send_sem x v Pr s h cl (t_send c (s v) mh (t_tau s h cl t_end))
  | send_failP : forall Pr (s: stack) (h mh: heap) (c: stptr) cl
    (Sref     : s x = vst c)
    (Sfail    : forall mh', ~ Marshal Pr (s v) h mh'),
    send_sem x v Pr s h cl t_fail
  .
  Program Definition send_cmd x v := Build_semCmd (send_sem x v) _.
  Next Obligation.
    intros H; inversion H.
  Qed.
(*
  Next Obligation with auto using send_sem.
    unfold frame_property; intros.
    inversion HSem. subst; clear HSem.
	exists h.
	split; [assumption |].
	destruct (Marshal_decidable Pr (s' v) h).
	destruct H.
	assert (x0 === mh).
	eapply Marshal_func. eapply Marshal_uc_heap. exists frame; apply HFrame. apply H. apply Smarshal.
	assert (Marshal Pr (s' v) h mh) by admit (* fangel, needs morphism so we can rewrite *).
	eapply send_ok; eassumption.
	exfalso; eapply HSafe; [reflexivity | apply trace_appendEndR |].
	eapply send_failP; eassumption.
  Qed.
*)


  Inductive recv_sem (v x : var) : semCmdType :=
  | recv_ok : forall Pr (s: stack) (h rh h': heap) (c: stptr) (rv : sval) cl
    (Sref: s x = vst c),
    recv_sem v x Pr s h cl 
      (t_recv c (fun rv rh => let (rv', h') := dmerge_heap rv rh h in 
                                  (t_tau (stack_add v (vptr rv') s) h' cl t_end)))
  .
  Program Definition recv_cmd v x := Build_semCmd (recv_sem v x) _.
  Next Obligation.
    intros H; inversion H.
  Qed.
  Next Obligation.
    unfold frame_property; intros.
    inversion HSem. subst; clear HSem.
    remember (update (elt:=val) h rh) as h'.
    exists h'.
    split.
    * apply sa_mulC in HFrame.
      eapply sa_mulA in Snewheap; [| apply HFrame].
      destruct Snewheap as [h'0 [H0 Snewheap]].
      destruct (heap_eq_dec h'0 h') as [Heq | Hneq].
      + apply sa_mulC in Snewheap.
        eapply sa_mul_mon. apply Heq. apply Snewheap.
      + assert (h'0 === (update (elt:=val) h rh)). {
          eapply sa_mul_MapResEq. apply H0.
          apply Disjoint_sa_mul. eapply sa_mul_Disjoint. apply H0.
        }
        rewrite <- Heqh' in H.
        exfalso. apply Hneq. apply H.
    * eapply recv_ok; [apply Sref | ].
      rewrite Heqh'. apply Disjoint_sa_mul.
      apply sa_mulC in HFrame.
      eapply sa_mulA in Snewheap; [| apply HFrame].
      destruct Snewheap as [h'0 [H0 _]].
      apply sa_mul_Disjoint in H0.
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
  | call_failS : forall (P : Prog_wf) s h cl
      (HLFail  : forall mrec, ~ method_lookup P (C s) m mrec),
      call_sem rvar C m es c sc P 1 s h cl (t_tau t_end) None
  | call_failC : forall (P : Prog_wf) ps rexpr (s : stack) h n tr cl
      (HLookup : method_lookup P (C s) m (Build_Method ps c rexpr))
      (HLen    : length ps = length es)
      (HFail   : sc P n (create_stack ps (eval_exprs s es)) h cl tr None),
      call_sem rvar C m es c sc P (S n) s h cl (t_tau tr) None
  | call_failL : forall (P : Prog_wf) ps rexpr s h cl
      (HLookup : method_lookup P (C s) m (Build_Method ps c rexpr))
      (HLen    : length ps <> length es),
      call_sem rvar C m es c sc P 1 s h cl (t_tau t_end) None
  | call_ok    : forall (P : Prog_wf) ps rexpr (s sr : stack) (h hr : heap) tr n cl cl'
      (HLookup : method_lookup P (C s) m (Build_Method ps c rexpr))
      (HLen    : length ps = length es)
      (HSem    : sc P n (create_stack ps (eval_exprs s es)) h cl tr (Some (sr, (hr, cl')))),
      call_sem rvar C m es c sc P (S n) s h cl (t_tau tr)
        (Some (stack_add rvar (eval rexpr sr) s, (hr, cl'))).
  Program Definition call_cmd rvar C m es c sc := Build_semCmd (call_sem rvar C m es c sc) _ _.
  Next Obligation.
    intros H; inversion H.
  Qed.
  Next Obligation with eauto using call_sem.
    unfold frame_property; intros.
    inversion HSem; subst; clear HSem.
    edestruct (@cmd_frame sc) as [h1 [HFrame1 HSem1]]...
    intros k HLe ? ? Htr HFail.
    eapply (HSafe (S k)) with (tr' := t_tau tr'); [omega | rewrite Htr; reflexivity |]... 
  Qed.

  Inductive start_sem (C : class) (m : method) (x : var) (p : protocol) (c : cmd) (sc : semCmd)
    : semCmdType :=
  | start_failE   : forall (P : Prog_wf) (a : var) (chan : stptr) (s: stack) (tr : trace) (h : heap) (rexpr : dexpr) n cl
       (HFresh    : ~ NS.In chan cl)
       (HLookup   : method_lookup P C m (Build_Method (a::nil) c rexpr))
       (HSem      : sc P n (stack_add a (vst chan) (stack_empty _)) heap_unit cl tr None),
       start_sem C m x p c sc P (S n) s h cl (t_start chan tr t_end) None
  | start_ok      : forall (P : Prog_wf) (a : var) (chan : stptr) (s rs: stack) (h rh : heap) (tr : trace) (rexpr : dexpr) n cl cl'
       (HFresh    : ~ NS.In chan cl)
       (HLookup   : method_lookup P C m (Build_Method (a::nil) c rexpr))
       (HSem      : sc P n (stack_add a (vst chan) (stack_empty _)) heap_unit (NS.add chan cl) tr (Some (rs, (rh, cl')))),
       start_sem C m x p c sc P (S n) s h cl (t_start chan tr t_end) (Some ((stack_add x (vst chan) s), (h, cl'))).
  Program Definition start_cmd C m x p c sc := Build_semCmd (start_sem C m x p c sc) _ _.
  Next Obligation.
    intros H; inversion H.
  Qed.
  Next Obligation with eauto using start_sem.
    unfold frame_property; intros.
    inversion HSem; subst; clear HSem...
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
  (*| semarrread : forall x y es,
                   semantics (carrread x y es) (read_arr_cmd x y es)
  | semarrwrite : forall x es e,
                   semantics (carrwrite x es e) (write_arr_cmd x es e)
  | semarralloc : forall x (e : dexpr),
                    semantics (carralloc x e) (alloc_arr_cmd x e) *) 
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
    + (* assign *)
      rewrite SS'.singleton_iff in HNM; intros P s s0 h h0 cl cl' t n HAsgn;
      simpl in *; inversion HAsgn; subst.
      rewrite stack_lookup_add2; trivial.
    + (* skip *)
      intros P s s0 h h0 cl cl0 t n HSkip; simpl in *; inversion HSkip; subst; trivial. 
    + (* seq *)
      intros P s s0 h h0 cl cl0 tr n HSeq; simpl in *; inversion HSeq; subst.
      transitivity (s2 x).
      * eapply IHc1; [| eassumption | eassumption]; intros HIn; apply HNM;
        rewrite SS'.union_iff; auto.
      * eapply IHc2; [| eassumption | eassumption]; intros HIn; apply HNM;
        rewrite SS'.union_iff; auto.
    + (* if *)
      intros P s s0 h h0 cl cl0 t n HND; simpl in *; inversion HND; subst; clear HND.
      * inversion H6; subst.
        apply assume_inv in H8; destruct H8; subst.
        eapply IHc1; [| eassumption | eassumption]; intros HIn; apply HNM;
          rewrite SS'.union_iff; auto.
      * inversion H6; subst.
        apply assume_inv in H8; destruct H8; subst.
        eapply IHc2; [| eassumption | eassumption]; intros HIn; apply HNM;
        rewrite SS'.union_iff; auto.
    + (* while *)
      intros P s s0 h h0 cl cl0 t n HKl; simpl in *; inversion HKl; subst; clear HKl.
      apply assume_inv in H9; destruct H9; destruct H0; subst; simpl in *.
      remember (Some (s0, (h2, cl2))); induction H7; subst;
        [inversion Heqo; trivial | discriminate | discriminate |].
      transitivity (s1 x); simpl in *.
      * inversion H; subst; clear H.
        apply assume_inv in H9; destruct H9; subst.
        eapply IHc; eassumption.
      * apply IHkleene_sem; assumption.
    + (* write *)
      intros P s s0 h h0 cl cl0 t n HWr; simpl in *; inversion HWr; subst; reflexivity.
    + (* read *)
      rewrite SS'.singleton_iff in HNM; intros P s s0 h h0 cl cl0 t n HRd; simpl in *;
      inversion HRd; subst; rewrite stack_lookup_add2; trivial.
    + (* alloc *)
      rewrite SS'.singleton_iff in HNM; intros P s s0 h h0 cl cl0 t n Hal; simpl in *.
      inversion Hal; subst. rewrite stack_lookup_add2; [reflexivity | assumption].
    + (* dcall *)
      rewrite SS'.singleton_iff in HNM; intros P s s0 h h0 cl cl0 t n HCl; simpl in *;
      inversion HCl; subst; rewrite stack_lookup_add2; trivial.
    + (* scall *)
      rewrite SS'.singleton_iff in HNM; intros P s s0 h h0 cl cl0 t n HCl; simpl in *;
      inversion HCl; subst; rewrite stack_lookup_add2; trivial.
    + (* assert *)
      intros P s s0 h h0 cl cl0 t n HAs; inversion HAs; subst; reflexivity.
    + (* send *)
      intros P s s0 h h0 cl cl0 t n HSd; inversion HSd; subst; reflexivity.
    + (* recv *)
      rewrite SS'.singleton_iff in HNM; intros P s s0 h h0 cl cl0 t n HCl; simpl in *;
      inversion HCl; subst; rewrite stack_lookup_add2; trivial.
    + (* start *)
      rewrite SS'.singleton_iff in HNM; intros P s s0 h h0 cl cl0 t n HCl; simpl in *;
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
    intros sc n Hn Q HPQ sem R k m s h t cl HQR Hk Hv Hp.
    assert (m = 0) by omega.
    assert (k = 0) by omega.
    subst. split.
    + intros ? ? HSem. apply cmd_zero in HSem. contradiction.
    + intros t' h' s'' cl' Hc. apply cmd_zero in Hc. contradiction.
  Qed.

(* Arguments swapped to please the type classes *)

  Definition typeof (C : class) (v : val) : Prop := exists p, v = vptr p /\ snd p = C.
  
  Program Definition typeof_asn (C : class) (v : val) : asn :=
    mk_asn (fun h Pr n => typeof C v) _ _ _.
    
  Notation " x ':::' C " := (`typeof_asn `C x/V) (at level 60).
  
(*

  (* TODO: should P,Q be allowed to reference stack vars from the outside? *)
  Definition expr_spec x m (ps: list var) (r: var) (P Q: hasn) : hasn :=
    (<E> C, <pure> x:::C </\> lift0 (FunI (C:.:m |-> ps {{P}}-{{r,Q}})))
    %asn.

  Arguments Scope expr_spec [_ _ _ _ asn_scope asn_scope].

  Notation " x ':..:' m |-> ps {{ P }}-{{ r , Q }} " :=
    (expr_spec x m ps r P Q) (at level 60).
*)

  Program Definition field_exists (C : class) (f : field) : spec :=
    mk_spec (fun Pr n =>
      exists fields, field_lookup Pr C fields /\ SS.In f fields
    ) _ _.
  Next Obligation.
    exists H. auto.
  Defined.
  Next Obligation.
    unfold field_lookup in H1; destruct H1 as [? [Hmt Heqf]].
    unfold Prog_wf_sub, Prog_sub in H.
    apply SM.find_1 in Hmt. specialize (H _ _ Hmt).
    destruct H as [? [HMT [Hequivf Hequivm]]].
    remember x0; destruct x0.
    exists c_fields; split.
    * exists c.
      split; [ | subst; reflexivity].
      apply SM.find_2; apply HMT.
    * rewrite Heqf in H2; rewrite Hequivf in H2.
      rewrite Heqc in H2; simpl in H2.
      apply H2.
  Defined.



Require Import UUSepAlg.
  

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
  Check mk_asn.
SearchAbout stptr.
Require Import EqNat.
 Program Definition eq_asn Pr n h := mk_asn (fun Pr' m h' => Prog_wf_sub Pr Pr' /\ m <= n /\ (h <= h')%sa) _ _ _.
 Next Obligation.
	repeat split; try assumption; omega.
 Qed.
	Next Obligation.
	repeat split; try assumption; transitivity P; assumption.
	Qed.
	Next Obligation.
	repeat split; try assumption; transitivity h0; assumption.
	Qed.
	
 Fixpoint trace_to_st (z : var) (x : stptr) (n : nat) (Pr : Prog_wf) (tr : trace) : ST :=
  	match tr with 
  		| t_end => st_end
  		| t_send y v h tr' =>
  			if beq_nat x y then
  				st_send z (fun s => (eq_asn Pr n h)) (trace_to_st z x n Pr tr')
  			else
  				trace_to_st z x n Pr tr'
  		| t_recv y v h tr' =>
  			if beq_nat x y then
  				st_recv z (fun s => (eq_asn Pr n h)) (trace_to_st z x n Pr tr')
  			else
  				trace_to_st z x n Pr tr'
  		| t_start y tr' tr'' => trace_to_st z x n Pr tr''
  		| t_tau tr' => trace_to_st z x n Pr tr'
  	end.  

  Fixpoint trim_protocol (Pr : Prog_wf) (n : nat) (pr : STs) (tr : trace) : option (nat * STs) :=
    match tr with
      | t_end => Some (n, pr)
      | t_send x v h tr' => match (find x pr) with
          | Some (st_send z P T) => trim_protocol Pr (n - 1) (add x (subst_ST z v T) pr) tr'
          | _ => None
        end
      | t_recv x v h tr' => match (find x pr) with
          | Some (st_recv z P T) => trim_protocol Pr (n - 1) (add x (subst_ST z v T) pr) tr'
          | _ => None
        end
      | t_start x tr' tr'' => trim_protocol Pr (n - 1) (add x (trace_to_st "v" x n Pr tr'') pr) tr''
      | t_tau tr' => trim_protocol Pr (n - 1) pr tr'
    end.
  
  Lemma trim_protocol_dc (Pr : Prog_wf) (n m k : nat) (pr pr' : STs) (tr : trace) 
 	(H: trim_protocol Pr n pr tr = Some (m, pr')) (Hnm: n >= k) :
 	exists t, trim_protocol Pr k pr tr = Some (t, pr') /\ m >= t.
  Proof.
    generalize dependent n; generalize dependent pr; generalize dependent k; induction tr; intros.
    + simpl in *. inversion H; subst.
      exists k. intuition congruence.
    + simpl in *. destruct (find s pr); [|congruence].
      destruct s0. 
      * congruence.
      * eapply IHtr; [eapply H|omega].
      * congruence.
    + simpl in *. destruct (find s pr); [|congruence].
      destruct s0; try congruence.
      eapply IHtr; [eapply H|omega].
    + admit.
    + simpl in *. eapply IHtr; [eassumption | omega].
  Qed.
 
  Lemma test : ((True /\ True) /\ True ) /\ True.
  Proof.
    split.
    {
    split.
    {
    split.
    {
    apply I.
    }
    apply I.
    }
    apply I.
    }
    apply I.
  Qed.
      apply I.
    } {
      split. {
        apply I.
      } {
        split. {
          apply I.
        }
        apply I.
      }
    }
  Qed.
    -
    apply I.
    -
    apply I.
  Qed.
 
  Program Definition cfg_asn (cfg : stack * (heap * NS.t)) (tr : trace) (pr : STs) (Pr : Prog_wf) (n : nat) : psasn := 
    fun s pr' => mk_asn (fun P m h =>  
    	match trim_protocol Pr n pr tr with
    		| Some (k, pr'') => fst cfg = s /\ (h <= fst (snd cfg))%sa /\ pr = pr'' /\ m <= k /\ Prog_wf_sub Pr P
    		| None           => False
    	end) _ _ _.
  Next Obligation.
    remember (trim_protocol Pr n pr tr).
    symmetry in Heqo.
    destruct o; [|inversion H].
    destruct p.
    simpl in *.
    intuition; subst.
  Qed.
  Next Obligation.
    admit.
  Qed.
  Next Obligation.
    admit.
  Qed.
  
  Lemma rule_frame_ax_list (P Q R : psasn) c (xs: list var)
    (HMod : forall x, ~ List.In x xs -> c_not_modifies c x) :
    {[ P ]} c {[ Q ]} |--
    {[ P ** R ]} c {[ Q ** Exists vs, apply_subst R (subst_fresh vs xs) ]}.
  Proof.
    clear HMod.
    generalize dependent Q. generalize dependent P.
    induction c; intros P Q PP n H.
    admit.
    admit.
    intros sc PP' HPP' m Hmn HSpec PP'' k t s h cl pr HPP'' Hkm Htk [h1 [h2 [HSub [HP HR]]]].
    inversion HSpec; subst.
    (*
    specialize (H (seq_cmd sc1 sc2) PP' HPP' m Hmn HSpec PP'' k t s h cl pr HPP'' Hkm Htk).
    *)
    split. admit.
    intros tr h' s' cl' HSem.
    inversion HSem; subst.
    
    specialize (H (seq_cmd sc1 sc2) PP' HPP' m Hmn HSpec PP'' k (n0 + n1)).
    Check @Comp_partial.
    apply @Comp_partial with (P := cfg_asn (s1, (h3, cl1)) tr0 pr PP'' k s pr PP'') (n := n) (m := m).
    specialize (IHc1 P ltrue PP n).
    specialize (IHc2 ltrue Q PP n).
    simpl in H.
    
    
    Local Opaque ILPre_Ops.
    Local Opaque ILFun_Ops.
    
    simpl in *.
    intros.
    inversion H0; subst; simpl in *.
    unfold embed in H0.
    unfold triple. lforallR sc; apply lpropimplR; intro Hsc. lforallL sc. 
    apply lpropimplL; [assumption|].
	(*generalize dependent sc; induction c; intros; inversion Hsc; subst. *)
    intros PP ? HSpec PP' ? ? ? ? cl pr HPP' Hmn Hkm [h1 [h2 [HSub [HP HR]]]]; split.
    - destruct (HSpec _ m k s h cl pr HPP' Hmn Hkm) as [HS _]; [ | assumption].
      solve_model HP. exists h2; apply HSub.
    - intros.
      specialize (HSpec PP' m k s h1 cl pr HPP' Hmn Hkm HP).
      destruct HSpec as [HSafe HComp].
      specialize (HSafe tr); specialize (HComp tr).
      clear -HSafe HComp HSub HR HSub Hsc HMod H.
      Local Opaque ILPre_Ops.
      Local Opaque ILFun_Ops.

      induction Hsc; simpl in *.
      + admit.
      + admit.
      + admit.
      + admit.
      + admit.
      + inversion H; subst.
        
      + admit.
      + admit.
      + admit.
      + admit.
      + admit.
      + admit.
      + admit.
      + 
      inversion H. subst. simpl.
     (*
      destruct (@cmd_frame sc PP' s s' h h' h2 h1 cl cl' k tr) as [h'' [HBig Hc]]; [ assumption | | apply H |].
      + clear HMod.
        intros ? Hle ? ? Htr HFail.
        assert (m0 <= m) by omega.
        specialize (HSpec PP' m m0 s h1 cl pr HPP' Hmn H0 HP).
        clear HP HR.
        destruct HSpec as [HSafe _].
        specialize (HSafe _ _ HFail).
        generalize dependent s'; generalize dependent h'; generalize dependent cl'.
        generalize dependent k; generalize dependent s; generalize dependent h.
        generalize dependent tr'. generalize dependent tr''. generalize dependent t. generalize dependent m0.
        generalize dependent sc; induction c; intros; inversion Hsc; subst.
        * (* assert *)
          inversion H; subst.
          assert (tr' = t_tau t_end \/ tr' = t_end) by admit (* fangel, H7 *).
          destruct H1; subst; simpl in HSafe; contradiction HSafe; reflexivity.
        * (* skip *)
          admit.
        * (* seq *)
          specialize (IHc1 _ HL).
          specialize (IHc2 _ HR).
          
          inversion H; subst.
          inversion HFail; subst.
          assert (n <= m) by omega.
          specialize (IHc1 _ HSub _ H2). Hkm Hle). _ _ _ _ _ H9).
          admit.
          
      apply H.
      *)
      generalize dependent sc. induction c; intros; inversion Hsc; subst.
      + (* assign *)
        inversion H; subst.
        unfold sem_triple in HSpec. simpl in HSpec.
        specialize (HSpec _ _ _ _ _ cl' _  HPP' Hmn Hkm HP).
        destruct HSpec.
        unfold Comp.
        admit (* fangel, work-in-progress *).
      + (* skip *)
        admit (* fangel, work-in-progress *).
      + (* sequencing *)
        inversion H; subst.
        unfold sem_triple in HSpec. simpl in HSpec.
        specialize (HSpec _ _ _ _ _ cl' _  HPP' Hmn Hkm HP).
        destruct HSpec.
        unfold Comp.
        
        admit (* fangel, work-in-progress *).
      + (* if *)
        admit (* fangel, work-in-progress *).
      + (* while *)
        admit (* fangel, work-in-progress *).
      + (* write *)
        admit (* fangel, work-in-progress *).
      + (* read *)
        admit (* fangel, work-in-progress *).
      + (* alloc *)
        admit (* fangel, work-in-progress *).
      + (* dcall *)
        admit (* fangel, work-in-progress *).
      + (* scall *)
        admit (* fangel, work-in-progress *).
      + (* assert *)
        admit (* fangel, work-in-progress *).
  Admitted.

  Definition subst_mod_asn (R: psasn) (c: cmd) : psasn :=
    Exists vs, apply_subst R (subst_fresh vs (SS.elements (modifies c))).

  Lemma rule_frame_ax (P Q R : psasn) c : 
    {[ P ]} c {[ Q ]} |--
    {[ P ** R ]} c {[ Q ** subst_mod_asn R c ]}.
  Proof.
    unfold subst_mod_asn.
    apply rule_frame_ax_list. intros x HnotIn. apply modifies_syn_sem.
    rewrite SS'.In_elements_iff. assumption.
  Qed.

  Lemma rule_frame (P Q R : psasn) c G 
    (HPre : G |-- {[P]} c {[Q]}) :
    G |-- {[ P ** R ]} c {[ Q ** subst_mod_asn R c ]}.
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
  
  Lemma existentialise_triple (x : var) (P Q : psasn) c (G : spec) 
	(H : forall (v : val), G |-- {[@lembedand vlogic psasn _ _ (open_eq (x/V) (`v)) P]} c {[Q]}) :
    G |-- {[P]} c {[Q]}.
  Proof.
    eapply roc_pre; [apply existentialise_var with (x0 := x)|].
    rewrite <- exists_into_precond2. lforallR y. apply H.
  Qed.

End StructuralRules.