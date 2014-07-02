Require Import RelationClasses Setoid Morphisms Program. 
Require Import MapInterface MapFacts.
Require Import SepAlg SepAlgMap UUSepAlg SepAlgInsts Stack Lang Rel.

Local Existing Instance MapSepAlgOps.
Local Existing Instance MapSepAlg.
Local Existing Instance MapEquiv.
Local Existing Instance EquivPreorder.
Local Existing Instance UUMapSepAlg.

Definition heap_arr := Map [arrptr * nat, val].
Definition heap_arr_unit : heap_arr := @map_unit _ _ _ val.

Instance RelHeapArr : Rel heap_arr := _.
Instance PreorderHeapArr : PreOrder (@rel heap_arr RelHeapArr) := _.
Instance HeapArrSepAlgOps : SepAlgOps heap_arr := _.
Instance SepAlgHeapArr : UUSepAlg heap_arr := _.

Lemma dec_double_neg (P : Prop) (H : {P} + {~P}) : 
  P <-> ~~P.
Proof.
  split; intros HP.  
  + intros H1. apply H1. apply HP.
  + destruct H; [assumption|].
    contradiction HP.
Qed.

Fixpoint find_heap_arr (x : nat) (path : list nat) (h : heap_arr) : option val :=
  match path with 
    | nil    => None
    | y::nil => find (x, y) h
    | y::ys  => match find (x, y) h with
                  | Some (varr y) => find_heap_arr y ys h
                  | _             => None
                end
  end.

Fixpoint add_heap_arr (x : nat) (path : list nat) (h : heap_arr) (v : val) : option heap_arr :=
  match path with 
    | nil    => None
    | y::nil => Some (add (x, y) v h)
    | y::ys  => match find (x, y) h with
                  | Some (varr y) => add_heap_arr y ys h v
                  | _             => None
                end
    end.

Fixpoint eq_heap_arr (x : nat) (path : list nat) (h1 h2 : heap_arr) : Prop :=
  match path with
    | nil   => True
    | y::ys => match find (x, y) h1, find (x, y) h2 with
                 | Some (varr v1), Some (varr v2) => v1 = v2 /\ eq_heap_arr v1 ys h1 h2
                 | _, _ => False
               end
  end.

Definition in_heap_arr (x : nat) (path : list nat) (h : heap_arr) : Prop :=
  exists y, find_heap_arr x path h = Some y.

Fixpoint alloc_heap_arr (i dim : nat) (h : heap_arr) : heap_arr :=
  match dim with 
    | 0     => add (i, 0) null h
    | S dim => add (i, dim) null (alloc_heap_arr i dim h)
  end.

  Lemma find_heap_arr_dec (x : nat) (path : list nat) (h : heap_arr):
    {exists v, find_heap_arr x path h = Some v} + {~exists v, find_heap_arr x path h = Some v}.
  Proof.
    generalize dependent x; induction path; simpl in *; intros.
    + right. intros [v H]. congruence.
    + destruct path; simpl in *.
      * remember (find (x, a) h) as o; simpl in *.
        rewrite <- Heqo in *; destruct o.
        - left. exists s. reflexivity.
        - right. intros [v H]. congruence.
      * remember (find (x, a) h) as o; simpl in *; rewrite <- Heqo in *. 
        destruct o; [|right; intros [v H]; congruence].
        destruct s; try (right; intros [v H]; congruence).
        apply IHpath.
  Qed.

  Lemma in_heap_arr_dec (x : nat) (path : list nat) (h : heap_arr):
    {in_heap_arr x path h} + {~in_heap_arr x path h}.
  Proof.
    apply find_heap_arr_dec.
  Qed.

  Lemma find_heap_arr_frame arr path h h' v frame (H : find_heap_arr arr path h = Some v) 
        (HFrame : sa_mul h' frame h) (HValid : in_heap_arr arr path h') : 
    find_heap_arr arr path h' = Some v.
  Proof.
    generalize dependent arr; induction path; simpl in *; intros.
    + inversion H.
    + destruct path.
      * clear IHpath; simpl in *; rewrite <- find_mapsto_iff in H.
        unfold in_heap_arr in HValid. simpl in *.
        destruct HValid as [y HValid].
        destruct (sa_mul_mapstoR HFrame H) as [[H1 H2] | [H1 H2]].
        rewrite <- find_mapsto_iff. assumption.
        contradiction H2. rewrite in_find_iff.
        unfold arrptr in *; simpl in *; rewrite HValid. congruence.
      * simpl in *.
        unfold in_heap_arr in HValid; simpl in *.
        destruct HValid as [y HValid].
        remember (find (arr, a) h') as o.
        unfold val in *; simpl in *; destruct o;
        rewrite <- Heqo in HValid; rewrite <- Heqo; [|congruence].
        destruct s; try congruence.
        apply IHpath.
        assert (In (arr, a) h'). rewrite in_find_iff. 
        unfold arrptr in *; simpl in *. rewrite <- Heqo. congruence.
        destruct (sa_mul_inL HFrame H0).
        rewrite in_find_iff in H2.
        symmetry in Heqo. rewrite <- find_mapsto_iff in Heqo.
        destruct (sa_mul_mapstoL HFrame Heqo).
        rewrite find_mapsto_iff in H3. unfold val in *; simpl in *.
        unfold arrptr in *. rewrite H3 in H. (* TODO investigate unfold arrptr. *)
        apply H. 
        unfold in_heap_arr. exists y.
        apply HValid.
  Qed.

Opaque MapSepAlgOps.

  Lemma find_heap_arr_subheap x path h h' v 
        (H : find_heap_arr x path h = Some v)
        (Hh : SepAlg.subheap h h') :
    find_heap_arr x path h' = Some v.
  Proof.
    destruct Hh as [h'' Hh]; generalize dependent x.
    induction path; simpl in *; intros.
    + congruence.
    + destruct path.
      * rewrite <- find_mapsto_iff in H.
        destruct (sa_mul_mapstoL Hh H).
        rewrite <- find_mapsto_iff.
        apply H0.
      * remember (find (x, a) h) as o; destruct o; 
        unfold val in *; simpl in *; rewrite <- Heqo in H; [|congruence].
        destruct v0; try congruence.
        symmetry in Heqo; rewrite <- find_mapsto_iff in Heqo.        
        destruct (sa_mul_mapstoL Hh Heqo).
        rewrite find_mapsto_iff in H0. 
        unfold arrptr, val in *; simpl in *.
        rewrite H0.
        apply IHpath; apply H.
  Qed.

  Lemma add_heap_arr_frame arr path (h frame h' h'' : heap_arr) v (HFrame : sa_mul h frame h')
        (H : add_heap_arr arr path h' v = Some h'') (HIn : in_heap_arr arr path h) :
    exists h''', sa_mul h''' frame h'' /\ add_heap_arr arr path h v = Some h'''.
  Proof.
    generalize dependent arr; induction path; simpl; intros.
    + congruence.
    + destruct path.
      * inversion H; subst; clear H IHpath.
        exists (add (arr, a) v h); split; [|reflexivity].
        destruct HIn as [y HIn]; simpl in HIn.
        apply sa_mul_add. assumption.
        intros H. rewrite <- find_mapsto_iff in HIn.
        destruct (sa_mul_mapstoL HFrame HIn). apply H1. apply H.
      * destruct HIn as [y HIn]; simpl in HIn. 
        remember (find (arr, a) h) as o; simpl in *.
        rewrite <- Heqo in *.
        destruct o; [|congruence].
        destruct s; try congruence.
        symmetry in Heqo; rewrite <- find_mapsto_iff in Heqo.
        edestruct (sa_mul_mapstoL HFrame Heqo) as [H1 _].
        rewrite find_mapsto_iff in H1. 
        unfold arrptr in *; simpl in *. rewrite H1 in H.
        apply IHpath. apply H.
        exists y. apply HIn.
  Qed.
(*
  Lemma add_hear_arr_eq x path h h' v n (H : add_heap_arr x path h v = Some h') 
        (Hn : n < length path) :
    eq_heap_arr x (firstn n path) h h'.
  Proof.
    generalize dependent path; generalize dependent x.
    induction n; intros; simpl in *; [apply I|].
    destruct path; simpl in Hn; [omega|].
    assert (n < length path) by omega.
    destruct path; [simpl in *; omega|clear Hn; simpl in *].
    remember (find (x, n0) h) as o. 
    unfold arrptr in *; simpl in *.
    rewrite <- Heqo in *.
    destruct o; [|congruence].
    destruct s; try congruence.
    specialize (IHn _ (n1::path) H H0).
    
    
    destruct n; simpl in *.
    admit. rewrite <- Heqo in IHpath.
    generalize dependent path; generalize dependent x; 
    induction n; intros; simpl in *; [apply I|].
    destruct path; simpl in *; [apply I|].
    destruct path; simpl in *. omega.
    assert (n < length (n1 :: path)) by (simpl; omega).
    specialize (IHn a (n1::path) H H0).
    destruc
    
    assert (path <> nil). {
      intro Hfail.
      rewrite Hfail in H0; simpl in H0.
      omega.
    specialize (IHn H0 H1).
    simpl in *.
    destruct path; simpl in *.
    + inversion H; clear H. assert (n = 0) by omega; subst.
      simpl.
      SearchAbout find add.
    assert (n < S(length path)) by omega.
    
    destruct o.
    admi
    destruct o; [|destruct path; simpl in; [apply I|congruence]].
    destruct s; try (destruct path; simpl in; [apply I|congruence]).
    assert (n < length path) as H1 by omega.
    specialize (IHn H1).
    destruct path; simpl in *; [apply I|].
    destruct path; simpl in *.
    inversion H.
    assert (n = 0) by omega. rewrite H0 in IHn.
    simpl in *.
    destruct path; simpl in *; [apply I|].
    Lemma eq_heap_arr_cons x y (h h' : heap_arr) (p : nat) path (H : find (x, y) h = Some (varr p))
          (Heq : eq_heap_arr p (firstn (length path - 1) path) h h') :
      eq_heap_arr x (firstn (length path) (y::path)) h h'.
    Proof.
      admit.
    Qed.
    replace (length path - 0) with (length path) by omega.

    eapply eq_heap_arr_cons; [symmetry; eapply Heqo|].
    simpl.


    generalize dependent x.
    
    induction path; simpl in *; intros; [apply I|].


    eapply eq_heap_arr_cons; [symmetry; eapply Heqo|].
    apply IHpath. destruct path; simpl in *.
    inversion H. f_equal. rewrite H1.
    admit.
    apply H.
    destruct n; simpl in *. admit.
    destruct path; simpl in *. apply I.
    simpl in *.
    destruct path; simpl in *; [apply I|].
    destruct o; [|congruence].
    destruct s; try congruence.

    specialize (IHpath _ H).

    destruct path; simpl in *.
    + inversion H. 
      
rewrite add_eq_o.
    
    replace (length path - 0) in IHpath with (length path) by omega.
    admit.
      simpl.
    

  Lemma add_find_heap_arr x path h h' v (H : add_heap_arr x path h v = Some h') :
    find_heap_arr x path h' = Some v.
  Proof.
    generalize dependent x; generalize dependent v;
    induction path; simpl in *; intros; [congruence|].
    destruct path; simpl in *.
    + inversion H; clear H.
      rewrite add_eq_o; reflexivity.
    + remember (MapInterface.find (x, a) h) as o;
      unfold arrptr, val in *; simpl in *; destruct o;
      rewrite <- Heqo in H; [|congruence].
      destruct s; try congruence.
      specialize (IHpath _ _ H).
      destruct path; simpl in *.
      inversion H; clear H.
      assert (exists v, find (x, a) h' = Some (varr v)) by admit.      
      destruct H0 as [v' H0].
      unfold arrptr in *; simpl in *.
      rewrite H0. 
      apply IHpath.
      destruct path. inversion H; clear H.
      f_equal. rewrite <- H2 in H0.
      symmetry in H0.
      specialize (IHpath _ H).

      destruct path; simpl in *.
      inversion H.
apply IHpath.
      Print find_heap_arr.
      Print add_heap_arr.
      remember (MapInterface.find (x, a) h') as o. 
      unfold arrptr in *; simpl in *; rewrite <- Heqo0.
      destruct o.
  Qed.
*)