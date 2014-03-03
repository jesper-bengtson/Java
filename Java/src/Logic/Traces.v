Require Import ZArith.
Require Import MapInterface MapFacts.
Require Import SepAlg UUSepAlg SepAlgInsts SepAlgMap.
Require Import Lang Program AssertionLogic HeapArr.
Require Import OrderedType Morphisms.

Import SepAlgNotations.

Inductive marshall (v : sval) (big : heap) : heap -> Prop :=
  | marshall_int  : forall (z : Z)
                    (Vint : v = vint z),
                    marshall v big heap_unit
  | marshall_bool : forall (b : bool)
                    (Vbool : v = vbool b),
                    marshall v big heap_unit
  | marshall_ptr  : forall (ref : ptr) (f : field) (v' : sval) (m : heap)
                    (Varr : v = vptr ref)
                    (Mmaps : MapsTo (ref, f) v' (get_heap_ptr big))
                    (Mmarshalls : marshall v' big m),
                    marshall v big (heap_add_ptr m ref f v')
  (*| marshall_ptr  : forall (ref : ptr) (m : heap)
                    (Vptr : v = vptr ref)
                    (Mhasfields : exists f, In (ref, f) (get_heap_ptr big))
                    (Mmarshalls :  forall (f : field) (v' : sval)
                    	(Mmaps : MapsTo (ref,f) v' (get_heap_ptr big)), 
                    	marshall v' big m /\ MapsTo (ref,f) v' (get_heap_ptr m))
                  	(Msubheap : subheap m big),
                    marshall v big m*)
  | marshall_arr  : forall (ref : arrptr) (i : nat) (v' : sval) (m : heap)
                    (Varr : v = varr ref)
                    (Mmaps : MapsTo (ref, i) v' (get_heap_arr big))
                    (Mmarshalls : marshall v' big m),
                    marshall v big (heap_add_arr m ref i v')
  .

Inductive trace : Type :=
  | tinit  : trace
  | tstart : trace -> trace -> trace
  | tsend  : sval -> heap -> trace -> trace
  | trecv  : sval -> heap -> trace -> trace
  .

Instance trace_Equivalance : Equivalence (@eq trace) := _.

Inductive trace_lte : relation trace :=
  | tlte_eq : forall t, trace_lte t t
  | tlte_start : forall t t' t'', trace_lte t t' -> trace_lte t (tstart t'' t')
  | tlte_send : forall t v h t', trace_lte t t' -> trace_lte t (tsend v h t')
  | tlte_recv : forall t v h t', trace_lte t t' -> trace_lte t (trecv v h t')
  .

Instance trace_Reflexive : Reflexive trace_lte.
Proof.
  intro x; constructor.
Qed.

Instance trace_Transitive : Transitive trace_lte.
Proof.
  intros x y z Hxy Hyz.
  inversion Hxy; try assumption; (
    induction Hyz; try apply Hxy; (constructor; apply IHHyz; [apply Hxy | apply H1])
  ).
Qed.

(*
It should also be anti-symmetrical, that is if a <= b and b <= a, then a = b,
but this was less trivial to prove...
Instance trace_Antisymmetric : Antisymmetric trace eq trace_lte.
*)

Instance trace_PreOrder : PreOrder trace_lte := Build_PreOrder trace trace_lte _ _.

Definition traces := Map [stptr, trace].

Definition traces_lte : relation traces := fun (t t' : traces) => forall k v, MapsTo k v t -> exists v', MapsTo k v' t' /\ trace_lte v v'.

Instance traces_Reflexive : Reflexive traces_lte.
Proof.
  intros x k v Hmt.
  exists v.
  split; [ assumption | apply tlte_eq ].
Qed.

Instance traces_lte_m : Proper (Equal ==> Equal ==> iff) traces_lte.
Proof.
  intros x y Hxy u t Hut; split; intro Hlte;
  unfold traces_lte in *;
  intros k v Hmt;
  specialize (Hlte k v);
  [ rewrite <- Hxy in Hmt | rewrite Hxy in Hmt ];
  apply Hlte in Hmt; clear Hlte;
  destruct Hmt as [v' [Hmt Htlte]];
  exists v';
  (split; [| apply Htlte]);
  [ rewrite <- Hut | rewrite Hut ];
  apply Hmt.
Qed.

Instance traces_Transitive : Transitive traces_lte.
Proof.
  intros x y z Hxy Hyz.
  intros k v Hmt.
  unfold traces_lte in *.
  specialize (Hxy k v).
  apply Hxy in Hmt; destruct Hmt as [v' [Hmt Hlte]]; clear Hxy.
  specialize (Hyz  k v').
  apply Hyz in Hmt; destruct Hmt as [v'' [Hmt' Hlte']]; clear Hyz.
  exists v''.
  split; [apply Hmt' | transitivity v'; assumption].
Qed.

Instance traces_PreOrder : PreOrder traces_lte := Build_PreOrder traces traces_lte _ _.

Lemma traces_lte_equal : forall t t', t === t' -> traces_lte t t'.
Proof.
  intros.
  rewrite H.
  reflexivity.
Qed.

Lemma traces_lte_new : forall t k v, ~In k t -> traces_lte t (add k v t).
Proof.
  intros t k v Hnotin k' v' Hmt.
  destruct (eq_dec k k').
  * exfalso; apply Hnotin.
    unfold In; exists v'.
    rewrite H.
    apply Hmt.
  * exists v'.
    split; [ | reflexivity].
    apply zadd_2; [ apply H | apply Hmt ].
Qed.

Lemma traces_lte_existing : forall t k v v', MapsTo k v t -> trace_lte v v' -> traces_lte t (add k v' t).
Proof.
  intros t k v v' Hmt Hlte k' v'' Hmt'.
  destruct (eq_dec k k').
  * rewrite <- H in *.
    assert (v = v''). {
      apply find_mapsto_iff in Hmt;
      apply find_mapsto_iff in Hmt'.
      rewrite Hmt in Hmt'.
      inversion Hmt'.
      reflexivity.
    }
    rewrite <- H0.
    exists v'.
    split; [apply zadd_1; auto | apply Hlte ].
  * exists v''.
    split; [| reflexivity ].
    apply zadd_2;[ apply H | apply Hmt' ].
Qed.

Lemma marshall_subheap {h h' : heap} {v : sval}
    (Hmarshall : marshall v h h') :
    subheap h' h.
Proof.
  assert (sa_unit heap_unit).
    unfold heap_unit; split; simpl; intuition.

  induction Hmarshall.
  + unfold subheap. exists big.
    apply sa_mulC.
    apply uusa_unit; assumption.
  + unfold subheap. exists big.
    apply sa_mulC.
    apply uusa_unit; assumption.
  + unfold subheap in IHHmarshall; destruct IHHmarshall as [h'' IHHmarshall].
    unfold subheap; exists (mkheap (remove (ref, f) (get_heap_ptr h'')) (get_heap_arr h'')).
    unfold heap_add_ptr.
    apply split_heap; [ repeat rewrite remove_mkheap_ptr | repeat rewrite remove_mkheap_arr ].
    * apply sa_mul_swapL; [apply IHHmarshall | apply Mmaps].
    * apply IHHmarshall. 
  + unfold subheap in IHHmarshall; destruct IHHmarshall as [h'' IHHmarshall].
    unfold subheap; exists (mkheap (get_heap_ptr h'') (remove (ref, i) (get_heap_arr h''))).
    unfold heap_add_arr.
    apply split_heap; [ repeat rewrite remove_mkheap_ptr | repeat rewrite remove_mkheap_arr ].
    * apply IHHmarshall.
    * apply sa_mul_swapL; [apply IHHmarshall | apply Mmaps].
Qed.

Lemma marshall_into_unit {m b} {v : sval}
    (Hempty : m === heap_unit) (Hmarshall : marshall v b m) :
    forall h, marshall v h m.
Proof.
  intro h.
  inversion Hmarshall.
  + eapply marshall_int; apply Vint.
  + eapply marshall_bool; apply Vbool.
  + destruct m as [m_ptr m_arr].
    assert (m_ptr === heap_ptr_unit) as Hempty_ptr by (apply Hempty).
    assert (Empty m_ptr) by (rewrite Hempty_ptr; intuition).
    unfold heap_add_ptr in H; simpl in H; unfold mkheap in H.
    inversion H.
    assert (MapsTo (ref, f) v' m_ptr) by (rewrite <- H2; apply add_1; reflexivity).
    unfold Empty in H0; specialize (H0 (ref, f) v').
    exfalso; auto.
  + destruct m as [m_ptr m_arr].
    assert (m_arr === heap_arr_unit) as Hempty_arr by (apply Hempty).
    assert (Empty m_arr) by (rewrite Hempty_arr; intuition).
    unfold heap_add_arr in H; simpl in H; unfold mkheap in H.
    inversion H.
    assert (MapsTo (ref, i) v' m_arr) by (rewrite <- H3; apply add_1; reflexivity).
    unfold Empty in H0; specialize (H0 (ref, i) v').
    exfalso; auto.
Qed.

Lemma marshall_into_smaller {a b c m : heap} {v : sval}
    (Habc : sa_mul a b c) (Hmarshall : marshall v c m)
    (Hdisjoint: DisjointHeaps b m) :
    marshall v a m \/ m === heap_unit.
Proof.
  induction Hmarshall; try auto; left.
  + constructor; try assumption.
    * eapply sa_mul_mapstoR in Mmaps; [| apply Habc].
      destruct Mmaps as [Mmaps | Mmaps]; destruct Mmaps as [Mmaps Mnotin]; [apply Mmaps|].
      unfold DisjointHeaps in Hdisjoint; destruct Hdisjoint as [Hdisjoint _].
      unfold Disjoint in Hdisjoint; specialize (Hdisjoint (ref, f)).
      exfalso; apply Hdisjoint. split.
      - unfold In; exists v'. assumption.
      - simpl. apply add_in_iff; auto. 
    * assert (DisjointHeaps b m). {
        unfold DisjointHeaps in *. destruct Hdisjoint as [Hdisjoint_ptr Hdisjoint_arr].
        split; [| apply Hdisjoint_arr]. simpl in Hdisjoint_ptr.
        unfold Disjoint in *. intro k. specialize (Hdisjoint_ptr k).
        intro Hcounter; apply Hdisjoint_ptr.
        destruct Hcounter as [Hcounter_b Hcounter_h'].
        split; [apply Hcounter_b|].
        destruct (eq_dec k (ref, f)); apply add_in_iff; auto.
      }
      apply IHHmarshall in Habc; [| apply H].
      destruct Habc; auto.
      eapply marshall_into_unit; [apply H0 | apply Hmarshall].
  + constructor; try assumption.
    * eapply sa_mul_mapstoR in Mmaps; [| apply Habc].
      destruct Mmaps as [Mmaps | Mmaps]; destruct Mmaps as [Mmaps Mnotin]; [apply Mmaps|].
      unfold DisjointHeaps in Hdisjoint; destruct Hdisjoint as [_ Hdisjoint].
      unfold Disjoint in Hdisjoint; specialize (Hdisjoint (ref, i)).
      exfalso; apply Hdisjoint. split.
      - unfold In; exists v'. assumption.
      - simpl. apply add_in_iff; auto.
    * assert (DisjointHeaps b m). {
        unfold DisjointHeaps in *. destruct Hdisjoint as [Hdisjoint_ptr Hdisjoint_arr].
        split; [apply Hdisjoint_ptr |]. simpl in Hdisjoint_arr.
        unfold Disjoint in *. intro k. specialize (Hdisjoint_arr k).
        intro Hcounter; apply Hdisjoint_arr.
        destruct Hcounter as [Hcounter_b Hcounter_h'].
        split; [apply Hcounter_b|].
        destruct (eq_dec k (ref, i)); apply add_in_iff; auto.
      }
      apply IHHmarshall in Habc; [| apply H].
      destruct Habc; auto.
      eapply marshall_into_unit; [apply H0 | apply Hmarshall].
Qed.

Lemma marshall_from_smaller {a b m : heap} {v : sval}
    (Hsubheap : subheap a b) (Hmarshall : marshall v a m) :
    marshall v b m.
Proof.
  induction Hmarshall.
  * eapply marshall_int; apply Vint.
  * eapply marshall_bool; apply Vbool.
  * eapply marshall_ptr. 
    + apply Varr.
    + unfold subheap in Hsubheap; destruct Hsubheap as [h Hsubheap].
      eapply sa_mul_mapstoL in Mmaps as [Mmaps Mnotin]; [| apply Hsubheap].
      apply Mmaps.
    + apply IHHmarshall; apply Hsubheap.
  * eapply marshall_arr. 
    + apply Varr.
    + unfold subheap in Hsubheap; destruct Hsubheap as [h Hsubheap].
      eapply sa_mul_mapstoL in Mmaps as [Mmaps Mnotin]; [| apply Hsubheap].
      apply Mmaps.
    + apply IHHmarshall; apply Hsubheap.
Qed.

Lemma marshall_fails_outside {a b c m : heap} {v : sval}
    (Habc : sa_mul a b c) (Hmarshall : marshall v c m)
    (Hdisjoint: ~ DisjointHeaps b m) :
    ~ marshall v a m \/ m === heap_unit.
Proof.
  destruct (heap_eq_dec m heap_unit) as [Heq | Hneq]; [right; assumption |].
  apply overlapping_exists in Hdisjoint.
  destruct Hdisjoint.
  * destruct H as [ref [f [Hinb Hinm]]].
    assert (sa_mul (get_heap_ptr a) (get_heap_ptr b) (get_heap_ptr c)) as Habc_ptr by (apply Habc).
    apply sa_mulC2 in Habc_ptr.
    eapply sa_mul_inL in Habc_ptr; [ |apply Hinb]; destruct Habc_ptr as [Hnotina _].
    left; intro Hcounter.
    apply marshall_subheap in Hcounter.
    unfold subheap in Hcounter; destruct Hcounter as [d Hcounter].
    apply Hnotina.
    eapply sa_mul_inL; [apply Hcounter | apply Hinm].
  * destruct H as [ref [i [Hinb Hinm]]].
    assert (sa_mul (get_heap_arr a) (get_heap_arr b) (get_heap_arr c)) as Habc_arr by (apply Habc).
    apply sa_mulC2 in Habc_arr.
    eapply sa_mul_inL in Habc_arr; [ |apply Hinb]; destruct Habc_arr as [Hnotina _].
    left; intro Hcounter.
    apply marshall_subheap in Hcounter.
    unfold subheap in Hcounter; destruct Hcounter as [d Hcounter].
    apply Hnotina.
    eapply sa_mul_inL; [apply Hcounter | apply Hinm].
Qed.
  