Require Import OrderedType OrderedTypeEx.
Require Import SepAlgMap.
Require Import Lang.
Require Import String.
Require Import MapInterface MapFacts.
Require Import AssertionLogic.

Local Existing Instance SvalEqEquiv.
Local Existing Instance OrderedTypeSval.
Local Instance EquivalencePtr : Equivalence (@prod_eq nat class _ stringEq) := _.
Local Instance EquivalenceRef : Equivalence (@prod_eq ptr field _ stringEq) := _.
Local Instance EquivalenceHeapPtr : Equivalence (Equal (elt:=(nat*class)%type)) := _.
(*
Inductive map_lt {A B : Type} {OTA : OrderedType A} {OTB : OrderedType B} : Map [A, B] -> Map [A, B] -> Prop :=
| map_elements_lt (a b : Map [A, B]) : elements a <<< elements b -> map_lt a b.

Definition map_compare {A B : Type} {OTA : OrderedType A} {OTB : OrderedType B} (a b : Map [A, B]) : comparison :=
  list_compare (elements a) (elements b).

Lemma empty_find_iff {A B : Type} {OTA : OrderedType A} {m : Map [A, B]}
  (Hempty : Empty m) : forall (k : A), find k m = None.
Proof.
  intro.
  apply not_find_in_iff.
  intro Hcounter.
  unfold In in Hcounter; destruct Hcounter as [v Hcounter].
  unfold Empty in Hempty.
  specialize (Hempty k v).
  auto.	
Qed.

Lemma elements_eqlistA_Equal {A B : Type} {OTA : OrderedType A} (m m' : Map [A, B]) :
  eqlistA K.eqke (elements m) (elements m') -> @Equal A OTA _ _ m m'.
Proof.
  intro Heql.
  remember (elements m) as lm.
  remember (elements m') as lm'.
  generalize dependent m. generalize dependent m'.
  induction Heql.
  * intros.
    symmetry in Heqlm; apply elements_Empty in Heqlm.
    symmetry in Heqlm'; apply elements_Empty in Heqlm'.
    unfold Equal.
    intro k.
    repeat (rewrite empty_find_iff; [| assumption]).
    reflexivity.
  * intros.
    destruct x as [k v]; destruct x' as [k' v'].
    inversion H. simpl in *.
    unfold Equal.
    intro k''.
    destruct (eq_dec k k'').
    + rewrite <- H2.
      assert (InA eq_key_elt (k, v) (elements m)) by (rewrite <- Heqlm; constructor; auto).
      assert (InA eq_key_elt (k, v) (elements m')) by (rewrite <- Heqlm'; constructor; auto).
      apply elements_mapsto_iff in H3; apply find_mapsto_iff in H3; rewrite H3; clear H3.
      apply elements_mapsto_iff in H4; apply find_mapsto_iff in H4; rewrite H4; clear H4.
      reflexivity.
    + assert (l' = elements (remove k' m')) by admit.
      assert (l = elements (remove k m)) by admit.
      specialize (IHHeql (remove k' m')).
      eapply IHHeql in H3; [| apply H4].
      unfold Equal in H3. specialize (H3 k'').
      rewrite remove_neq_o in H3; [| auto].
      rewrite remove_neq_o in H3; [ apply H3 | ].
      intro Hcounter. apply H2.
      transitivity k'; assumption.
Qed.

Lemma remove_subst {A B : Type} {OTA : OrderedType A} (m m' : Map [A, B])
  (H : m === m') : forall (k : A), remove k m === remove k m'.
Proof.
  unfold "===", Equal.
  intros k k'.
  destruct (eq_dec k k').
  * repeat (rewrite remove_eq_o; [| assumption]); reflexivity.
  * repeat (rewrite remove_neq_o; [| assumption]).
    unfold "===", Equal in H.
    apply H.
Qed.

Lemma elements_remove {A B : Type} {OTA : OrderedType A} (m : Map [A, B]) (k : A) (v : B) (l : list (A * B))
  (H : (k, v) :: l = elements m) : l = elements (remove k m).
Proof.
  generalize dependent m; generalize dependent v; generalize dependent k.
  induction l.
  * intros k v m H.
    assert (empty B === remove k (add k v (empty B))). {
      unfold "===", Equal.
      intro k'.
      destruct (eq_dec k k'); rewrite empty_o.
      * rewrite remove_eq_o; [reflexivity | assumption].
      * rewrite remove_neq_o; [| assumption].
        rewrite add_neq_o; [| assumption].
        rewrite empty_o.
        reflexivity.
    }
    assert (m === add k v (empty B)). {
      unfold "===", Equal.
      intro k'.
      destruct (eq_dec k k').
      * rewrite add_eq_o; [| assumption].
        apply find_mapsto_iff.
        apply elements_mapsto_iff.
        rewrite <- H.
        constructor; auto.
      * rewrite add_neq_o; [| assumption].
        rewrite empty_o.
        apply not_find_in_iff.
        intro Hcounter.
        unfold In in Hcounter; destruct Hcounter as [v' Hcounter].
        apply elements_mapsto_iff in Hcounter.
        rewrite <- H in Hcounter.
        inversion Hcounter; inversion H3. subst.
        simpl in *.
        auto.
    }
    assert (empty B === remove k m). {
      eapply remove_subst in H1.
      symmetry in H1.
      transitivity (remove k (add k v (empty B))).
      apply H0.
      apply H1.
    }
    apply elements_Equal_eqlistA in H2.
    rewrite elements_empty in H2.
    inversion H2.
    reflexivity.
  * intros k v m H.
    destruct a as [k' v'].
    admit.
Admitted.

Local Instance StrictOrderMap {A B : Type} {OTA : OrderedType A} {OTB : OrderedType B} : StrictOrder (@map_lt A B OTA OTB) (Equal (elt:=B)).
Proof.
  admit.
  (*
  split.
  * intros a b c Hab Hbc.
    inversion Hab; subst.
    inversion Hbc; subst.
    constructor;  transitivity (elements b); assumption.
  * intros x y Hxy H. induction Hxy.
    remember (elements a) as la.
    remember (elements b) as lb.
    generalize dependent a.
    generalize dependent b.
    induction H0.
    + intros. destruct a as [k v].
      unfold "===", Equal in H; specialize (H k).
      symmetry in Heqla; apply elements_Empty in Heqla.
      assert (InA eq_key_elt (k, v) (elements b)). {
        rewrite <- Heqlb. constructor. constructor; auto.
      }
      apply elements_mapsto_iff in H0.
      apply find_mapsto_iff in H0; rewrite H0 in H; clear H0.
      rewrite empty_find_iff in H; [| apply Heqla].
      inversion H.
    + intros. destruct a as [k v]; destruct a' as [k' v'].
      unfold "===" in H0.
      assert (eqlistA K.eqke (elements a0) (elements b)) by (apply elements_Equal_eqlistA; apply H0).
      rewrite <- Heqla in H1; rewrite <- Heqlb in H1.
      inversion H1; subst; clear H1; clear H7.
      inversion H5; clear H5; simpl in *.
      inversion H; subst.
      - assert (k <<< k') by (apply H4).
        symmetry in H1. apply eq_not_gt in H1.
        auto.
      - assert (v' === v') by auto.
        assert (v' <<< v') by (apply H8).
        apply eq_not_gt in H2.
        auto.
    + intros.
      assert (eqlistA K.eqke (elements a0) (elements b)) by (apply elements_Equal_eqlistA; apply H1).
      rewrite <- Heqla in H2; rewrite <- Heqlb in H2.
      inversion H2; subst; clear H2.
      destruct a as [k v]; destruct a' as [k' v'].
      assert (eqlistA K.eqke l' (elements (remove k' b))) by admit.
      assert (eqlistA K.eqke l (elements (remove k a0))) by admit.
      assert (eqlistA K.eqke l (elements (remove k' b))).
        transitivity l'; assumption.
      assert (eqlistA K.eqke (elements (remove k a0)) (elements (remove k' b))).
        transitivity l; [symmetry |]; assumption.
      apply elements_eqlistA_Equal in H5; clear H4.
      eapply IHlist_lt.
      apply H2.
      apply H3.
      apply H5.
      *)
Qed.

Program Instance OrderedTypeHeapPtr : OrderedType heap_ptr := Build_OrderedType heap_ptr Equal map_lt _ _ map_compare _.
Next Obligation.
  admit.
Qed.

Instance SOT_HeapPtr : SpecificOrderedType heap_ptr (@Equal (ptr*field)%type _ _ sval) := _.
Proof.
  

Lemma blah (a b : heap_ptr) : a === b.
Proof.
  destruct (eq_dec a b). simpl in *.
  apply H.
*)
