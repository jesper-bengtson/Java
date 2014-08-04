Require Import ILogic ILInsts SepAlg BILogic BILInsts IBILogic SepAlgMap Containers.Maps Strings.String Rel.
Require Import RelationClasses Setoid Morphisms Program. 
Require Import MapInterface MapFacts.
Require Import Open Stack Lang OpenILogic Pure ILEmbed PureInsts.
Require Import UUSepAlg SepAlgInsts.
Require Export HeapArr. (* Export on HeapArr so other files can just require Heap and get both heap, heap_ptr and heap_arr *)

Local Existing Instance MapSepAlgOps.
Local Existing Instance MapSepAlg.
Local Existing Instance MapEquiv.
Local Existing Instance EquivPreorder.
Local Existing Instance UUMapSepAlg.
Local Existing Instance SepAlgOps_prod.
Local Existing Instance SepAlg_prod.
Local Existing Instance UUSepAlg_prod.

Definition heap := Map [ptr * field, val].
Definition heap_unit : heap := @map_unit _ _ _ val.

Definition max_key (h : heap) : nat :=
	@fold (ptr * field) _ _ _ _ (fun p _ x => max (fst (fst p)) x) h 0.

Definition offset_val (v : val) (n : nat) : sval :=
	match v with
	  | vptr (x, C) => vptr (x + n, C)
	  | _ => v
	end.

Definition offset_heap (h : heap) (n : nat) : heap :=
	@fold (ptr * field) _ _ _ _ (fun p v acc => add ((((fst (fst p)) + n), snd (fst p)), snd p) (offset_val v n) acc)
		  h (@empty (ptr * field) _ _ _).
		  
Definition merge_heap (h1 h2 : heap) : heap :=
	@fold (ptr * field) _ _ _ _ add h1 h2.
	
Definition dmerge_heap (p : ptr) (h1 h2 : heap) : ptr * heap :=
    let n := max_key h2 in ((fst p + n, snd p), merge_heap (offset_heap h1 n) h2).

(*
Definition heap := (heap_ptr * heap_arr)%type.

Definition mkheap (hp: heap_ptr) (ha: heap_arr) := (hp, ha).
Definition get_heap_ptr (h: heap) : heap_ptr := fst h.
Definition get_heap_arr (h: heap) : heap_arr := snd h.

Definition heap_ptr_unit : heap_ptr := @map_unit _ _ _ val.
Definition heap_unit : heap := (heap_ptr_unit, heap_arr_unit).

Definition heap_add_ptr (h : heap) (p : ptr) (f : field) (v : val) : heap :=
  mkheap (add (p, f) v (get_heap_ptr h)) (get_heap_arr h) (*(get_heap_st h)*).
Definition heap_add_arr (h : heap) (n m : nat) (v : val) : heap :=
  mkheap (get_heap_ptr h) (add (n, m) v (get_heap_arr h)) (*(get_heap_st h)*).

Instance RelHeapPtr : Rel heap_ptr := _.
Instance PreorderHeapPtr : PreOrder (@rel heap_ptr RelHeapPtr) := _.
Instance HeapPtrSepAlgOps : SepAlgOps heap_ptr := _.
Instance SepAlgHeapPtr : SepAlg heap_ptr := _.
Instance UUSepAlgHeapPtr : UUSepAlg heap_ptr := _.
*)
Instance RelHeap : Rel heap := _.
Instance PreorderHeap : PreOrder (@rel heap RelHeap) := _.
Instance HeapSepAlgOps : SepAlgOps heap := _.
Instance SepAlgHeap : SepAlg heap := _.
Instance UUSepAlgHeap : UUSepAlg heap := _.

Import SepAlgNotations.

Lemma Empty_find_None {A B: Type} {HOT: OrderedType A} : forall (m: Map[A, B]) (k: A), Empty m -> find k m = None.
Proof.
  intros.
  rewrite <- not_find_in_iff.
  intro Hcounter.
  unfold Empty in H; unfold In in Hcounter.
  destruct Hcounter as [v Hcounter].
  specialize (H k v).
  apply H; assumption.
Qed. 

Lemma map_eq_dec {A B: Type} {HOT: OrderedType A} {Hequiv: Equivalence Equal} : forall (a b: Map[A, B]), {a === b} + {a =/= b}.
Proof.
  intros a.
  apply map_induction.
  * intros b Hempty_b.
    generalize dependent a.
    apply map_induction.
    + intros a Hempty_a.
      left.
      unfold "===", Equal.
      intros k.
      repeat rewrite Empty_find_None; [reflexivity | |]; assumption.
    + intros a a' Hdec k v Hnotin Hadd.
      right.
      intro Hcounter.
      unfold Empty in Hempty_b.
      specialize (Hempty_b k v).
      apply Hempty_b.
      rewrite <- Hcounter.
      unfold Add in Hadd.
      rewrite find_mapsto_iff, Hadd, add_eq_o; reflexivity.      
  * intros b b' Hdec k_b v_b Hnotin_b Hadd_b.
    clear Hdec.
    generalize dependent a.
    apply map_induction.
    + intros a Hempty_a.
      right.
      intro Hcounter.
      unfold Empty in Hempty_a.
      specialize (Hempty_a k_b v_b).
      apply Hempty_a.
      rewrite Hcounter.
      unfold Add in Hadd_b.
      rewrite find_mapsto_iff, Hadd_b, add_eq_o; reflexivity.
    + intros a a' Hdec k_a v_a Hnotin_a Hadd_a.
      destruct Hdec as [Heq|Hneq].
      - right.
        intro Hcounter.
        rewrite <- Heq in Hcounter.
        unfold "===", Equal in Hcounter.
        specialize (Hcounter k_a).
        unfold Add in Hadd_a.
        rewrite Hadd_a, add_eq_o in Hcounter; [| reflexivity].
        apply Hnotin_a.
        unfold In. exists v_a.
        rewrite find_mapsto_iff.
        congruence.
      - admit (* fangel, unused *).
Admitted.

Lemma heap_eq_dec : forall (a b : heap), {a === b} + {a =/= b}.
Proof.
  admit (* fangel, used *).
Qed.
(*
Lemma sa_mul_heapResEq {a b c c' : heap}
  (Habc : sa_mul a b c) (Habc' : sa_mul a b c') :
  c === c'.
Proof.
  destruct c as [c_ptr c_arr]; destruct c' as [c'_ptr c'_arr].
  split.
  * eapply sa_mul_MapResEq; [apply Habc | apply Habc'].
  * eapply sa_mul_MapResEq; [apply Habc | apply Habc'].
Qed.

Lemma isolate_heap_ptr : forall a b c, sa_mul a b c -> 
                         sa_mul (get_heap_ptr a) (get_heap_ptr b) (get_heap_ptr c).
Proof.
  intros.
  destruct a as [a_ptr a_arr], b as [b_ptr b_arr], c as [c_ptr c_arr].
  apply sa_mul_split in H as [Hptr Harr].
  apply Hptr.
Qed.

Lemma isolate_heap_arr : forall a b c, sa_mul a b c -> 
                         sa_mul (get_heap_arr a) (get_heap_arr b) (get_heap_arr c).
Proof.
  intros.
  destruct a as [a_ptr a_arr], b as [b_ptr b_arr], c as [c_ptr c_arr].
  apply sa_mul_split in H as [Hptr Harr].
  apply Harr.
Qed.

Lemma split_heap : forall a b c,
                   sa_mul (get_heap_ptr a) (get_heap_ptr b) (get_heap_ptr c) ->
                   sa_mul (get_heap_arr a) (get_heap_arr b) (get_heap_arr c) ->
                   sa_mul a b c.
Proof.
  intros.
  destruct a as [a_ptr a_arr], b as [b_ptr b_arr], c as [c_ptr c_arr].
  apply sa_mul_split; split; assumption. 
Qed.

Lemma remove_mkheap_ptr : forall Hptr Harr, get_heap_ptr (mkheap Hptr Harr) = Hptr.
  Proof. intros. reflexivity. Qed.
Lemma remove_mkheap_arr : forall Hptr Harr, get_heap_arr (mkheap Hptr Harr) = Harr.
  Proof. intros. reflexivity. Qed.

Definition DisjointHeaps (n m : heap) := Disjoint (get_heap_ptr n) (get_heap_ptr m) /\ Disjoint (get_heap_arr n) (get_heap_arr m).
*)
Lemma empty_is_disjoint {K A : Type} {H : OrderedType K} {a : Map [K, A]} (Hempty : Empty a) : forall b, Disjoint a b.
Proof.
  intros.
  unfold Disjoint. intros k Hcounter.
  destruct Hcounter as [Hcounter _].
  unfold In in Hcounter; destruct Hcounter as [v Hcounter].
  unfold Empty in Hempty; specialize (Hempty k v).
  auto.
Qed.
(*
Lemma DisjointHeaps_sa_mul {a b : heap} (H : DisjointHeaps a b) :
  sa_mul a b (mkheap (update (get_heap_ptr a) (get_heap_ptr b)) (update (get_heap_arr a) (get_heap_arr b))).
Proof.
  unfold DisjointHeaps in H; destruct H as [Hdisjoint_ptr Hdisjoint_arr].
  apply Disjoint_sa_mul in Hdisjoint_ptr.
  apply Disjoint_sa_mul in Hdisjoint_arr.
  apply split_heap; [ repeat rewrite remove_mkheap_ptr | repeat rewrite remove_mkheap_arr ]; assumption.
Qed.

Lemma sa_mul_DisjointHeaps {a b c : heap} (H : sa_mul a b c) :
  DisjointHeaps a b.
Proof.
  unfold DisjointHeaps; split;
  [apply isolate_heap_ptr in H|apply isolate_heap_arr in H];
  eapply sa_mul_Disjoint; apply H.
Qed.
*)