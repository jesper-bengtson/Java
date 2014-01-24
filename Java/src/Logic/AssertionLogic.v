(* This file is a monster. Working with type classes is great, but the mechanisms for
   creating an instance are currently very fragile. One major piece of work will be to
   make this easier. Ideally, this file should not be larger than a few tens of lines
   at most. *)

Require Import ILogic ILInsts SepAlg BILogic BILInsts IBILogic SepAlgMap Maps String Rel.
Require Import RelationClasses Setoid Morphisms Program. 
Require Import MapInterface MapFacts.
Require Import Open Stack Lang OpenILogic Pure ILEmbed PureInsts.
Require Import UUSepAlg SepAlgInsts HeapArr.

Local Existing Instance ILPre_Ops.
Local Existing Instance ILPre_ILogic.

Local Existing Instance ILFun_Ops.
Local Existing Instance ILFun_ILogic.
Local Existing Instance SAIBIOps.
Local Existing Instance SAIBILogic.
Local Existing Instance BILPre_Ops.
Local Existing Instance IBILPreLogic.
Local Existing Instance BILFun_Ops.
Local Existing Instance IBILFunLogic.

Local Existing Instance MapSepAlgOps.
Local Existing Instance MapSepAlg.
Local Existing Instance MapEquiv.
Local Existing Instance EquivPreorder.
Local Existing Instance UUMapSepAlg.
Local Existing Instance SepAlgOps_prod.
Local Existing Instance SepAlg_prod.
Local Existing Instance UUSepAlg_prod.

Definition heap_ptr := Map [ptr * field, val].

Definition heap := (heap_ptr * heap_arr)%type.

(* Definition mkheap (hp: heap_ptr) (ha: heap_arr) (hs: heap_st) := (hp, (ha, hs)). *)
Definition mkheap (hp: heap_ptr) (ha: heap_arr) := (hp, ha).
Definition get_heap_ptr (h: heap) : heap_ptr := fst h.
Definition get_heap_arr (h: heap) : heap_arr := snd h.
(* Definition get_heap_st  (h: heap) : heap_st  := snd (snd h). *)

Definition heap_ptr_unit : heap_ptr := @map_unit _ _ _ val.
(* Definition heap_unit : heap := (heap_ptr_unit, (heap_arr_unit, heap_st_unit)).*)
Definition heap_unit : heap := (heap_ptr_unit, heap_arr_unit).

Definition heap_add_ptr (h : heap) (p : ptr) (f : field) (v : val) : heap :=
  mkheap (add (p, f) v (get_heap_ptr h)) (get_heap_arr h) (*(get_heap_st h)*).
Definition heap_add_arr (h : heap) (n m : nat) (v : val) : heap :=
  mkheap (get_heap_ptr h) (add (n, m) v (get_heap_arr h)) (*(get_heap_st h)*).
(*Definition heap_add_st (h : heap) (p : stptr) (t : sST) : heap :=
  mkheap (get_heap_ptr h) (get_heap_arr h) (add p t (get_heap_st h)).*)

Instance RelHeapPtr : Rel heap_ptr := _.
Instance PreorderHeapPtr : PreOrder (@rel heap_ptr RelHeapPtr) := _.
Instance HeapPtrSepAlgOps : SepAlgOps heap_ptr := _.
Instance SepAlgHeapPtr : SepAlg heap_ptr := _.
Instance UUSepAlgHeapPtr : UUSepAlg heap_ptr := _.

Instance RelHeap : Rel heap := _.
Instance PreorderHeap : PreOrder (@rel heap RelHeap) := _.
Instance HeapSepAlgOps : SepAlgOps heap := _.
Instance SepAlgHeap : SepAlg heap := _.
Instance UUSepAlgHeap : UUSepAlg heap := _.

Import SepAlgNotations.

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

(*
Lemma isolate_heap_st : forall a b c, sa_mul a b c -> 
                         sa_mul (get_heap_st a) (get_heap_st b) (get_heap_st c).
Proof.
  intros.
  destruct a as [a_ptr [a_arr a_st]], b as [b_ptr [b_arr b_st]], c as [c_ptr [c_arr c_st]].
  apply sa_mul_split in H as [Hptr Harr]; apply sa_mul_split in Harr as [Harr Hst].
  apply Hst.
Qed.
*)

Lemma split_heap : forall a b c,
                   sa_mul (get_heap_ptr a) (get_heap_ptr b) (get_heap_ptr c) ->
                   sa_mul (get_heap_arr a) (get_heap_arr b) (get_heap_arr c) ->
                   (* sa_mul (get_heap_st a) (get_heap_st b) (get_heap_st c) -> *)
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
(*Lemma remove_mkheap_st : forall Hptr Harr Hst, get_heap_st (mkheap Hptr Harr Hst) = Hst.
  Proof. intros. reflexivity. Qed.*)

Definition DisjointHeaps (n m : heap) := Disjoint (get_heap_ptr n) (get_heap_ptr m) /\ Disjoint (get_heap_arr n) (get_heap_arr m).

Lemma empty_is_disjoint {K A : Type} {H : OrderedType K} {a : Map [K, A]} (Hempty : Empty a) : forall b, Disjoint a b.
Proof.
  intros.
  unfold Disjoint. intros k Hcounter.
  destruct Hcounter as [Hcounter _].
  unfold In in Hcounter; destruct Hcounter as [v Hcounter].
  unfold Empty in Hempty; specialize (Hempty k v).
  auto.
Qed.

Lemma empty_or_disjoint {K A : Type} {H : OrderedType K} {a b : Map [K, A]} :
  Disjoint a b \/ (exists (k : K), In k a /\ In k b).
Proof.
  destruct (is_empty_dec a); [left; apply empty_is_disjoint; assumption |].
  destruct (is_empty_dec b); [left; apply Disjoint_sym; apply empty_is_disjoint; assumption |].
  admit.
Admitted.

Lemma overlapping_exists : forall a b, ~ DisjointHeaps a b ->
  (exists ref f, In (ref, f) (get_heap_ptr a) /\ In (ref, f) (get_heap_ptr b))
  \/
  (exists ref i, In (ref, i) (get_heap_arr a) /\ In (ref, i) (get_heap_arr b)).
Proof.
  intros.
  unfold not in H; unfold DisjointHeaps in H.
  assert (Disjoint (get_heap_ptr a) (get_heap_ptr b) \/ (exists (k : (ptr * field)), In k (get_heap_ptr a) /\ In k (get_heap_ptr b))) by (apply empty_or_disjoint).
  assert (Disjoint (get_heap_arr a) (get_heap_arr b) \/ (exists (k : (arrptr * nat)), In k (get_heap_arr a) /\ In k (get_heap_arr b))) by (apply empty_or_disjoint).
  destruct H0; destruct H1.
  exfalso; auto.
  right. destruct H1 as [[ref i] H1].
  exists ref; exists i. assumption.
  left. destruct H0 as [[ref f] H0].
  exists ref; exists f. assumption.
  left. destruct H0 as [[ref f] H0].
  exists ref; exists f. assumption.
Qed.

Lemma DisjointHeaps_sa_mul {a b : heap} (Hdisjoint: DisjointHeaps a b) :
  sa_mul a b (mkheap (update (get_heap_ptr a) (get_heap_ptr b)) (update (get_heap_arr a) (get_heap_arr b))).
Proof.
  unfold DisjointHeaps in Hdisjoint; destruct Hdisjoint as [Hdisjoint_ptr Hdisjoint_arr].
  apply Disjoint_sa_mul in Hdisjoint_ptr.
  apply Disjoint_sa_mul in Hdisjoint_arr.
  apply split_heap; [ repeat rewrite remove_mkheap_ptr | repeat rewrite remove_mkheap_arr ]; assumption.
Qed.

(*
Definition merge (h1 h2 : heap_ptr) : heap_ptr :=
  fold (fun key val h => add key val h) h2 h1.

Definition this_level (val : sval) (h : heap_ptr) : heap_ptr :=
  match val with
    | vptr ref => filter (fun (key : (ptr * field)) _ => let (ref', f) := key in ref == ref') h
    | _ => empty _
  end.

Fixpoint test (n : nat) (val : sval) (h : heap_ptr) {struct n} : heap_ptr :=
  match val with
    | vptr ref => match n with
      | O => empty _
      | S n => let (here, rest) := partition (fun (key : (ptr * field)) _ => let (ref', f) := key in ref == ref') h in
             if is_empty here then empty _ else
             update here (fold (fun _ val' => update (test n val' rest)) here rest)
      end
    | _ => empty _
  end.
*)

Definition asn1 := ILPreFrm (@rel heap subheap) Prop.
Instance ILogicOpsAsn1 : ILogicOps asn1 := _.
Instance ILogicAsn1 : ILogic asn1 := _.


Definition asn2 := ILPreFrm ge asn1.
Instance ILogicOpsAsn2 : ILogicOps asn2 := _.
Instance ILogicAsn2 : ILogic asn2 := _.

Definition asn := ILPreFrm Prog_wf_sub asn2.
Instance ILogicOpsAsn : ILogicOps asn := _.
Instance ILogicAsn : ILogic asn := _.

Instance BILOperatorsAsn1 : BILOperators asn1 := _.
Instance BILOperatorsAsn2 : BILOperators asn2 := _.
Instance BILOperatorsAsn : BILOperators asn := _.

Instance BILogicAsn1 : BILogic asn1 := _.
Instance BILogicAsn2 : BILogic asn2 := _.
Instance BILogicAsn  : BILogic asn := _.

Instance IBILogicAsn1 : IBILogic asn1 := _.
Instance IBILogicAsn2 : IBILogic asn2 := _.
Instance IBILogicAsn  : IBILogic asn := _.

Local Existing Instance EmbedILPreDropOp.
Local Existing Instance EmbedILPreDrop.
Local Existing Instance EmbedOpPropProp.
Local Existing Instance EmbedPropProp.

Instance EmbedAsnPropOp : EmbedOp Prop asn := _.
Instance EmbedAsnProp : Embed Prop asn := _.

Definition sasn := @open var _ asn.

Instance ILOpsSAsn : ILogicOps sasn := _.
Instance ILogicSAsn : ILogic sasn := _.
Instance BILOperatorsSAsn : BILOperators sasn := _.
Instance BILogicSAsn : IBILogic sasn := _.

Local Existing Instance EmbedILFunDropOp.
Local Existing Instance EmbedILFunDrop.
Local Existing Instance EmbedILFunOp.
Local Existing Instance EmbedILFun.
Local Existing Instance EmbedILPreOp.
Local Existing Instance EmbedILPre.

Local Existing Instance SABIOps.
Local Existing Instance SABILogic.
Local Existing Instance pureop_bi_sepalg.

Instance EmbedSasnPureOp : EmbedOp vlogic sasn := _.
Instance EmbedSasnPure : Embed vlogic sasn := _.

Require Import SpecLogic.

Instance EmbedAsn1PropOp : EmbedOp Prop asn1 := _.
Instance EmbedAsn1Prop   : Embed Prop asn1 := _.
Instance EmbedAsn2SpecOp : EmbedOp spec1 asn2 := _.
Instance EmbedAsn2Spec   : Embed spec1 asn2 := _.
Instance EmbedAsnSpecOp  : EmbedOp spec asn := _.
Instance EmbedAsnSpec    : Embed spec asn := _.
Instance EmbedSAsnSpecOp : EmbedOp spec sasn := _.
Instance EmbedSAsnSpec   : Embed spec sasn := _.

Local Existing Instance pure_embed_pre_drop.
Local Existing Instance pure_embed_pre.
Local Existing Instance pure_embed_fun_drop.
Local Existing Instance pure_embed_fun.
Local Existing Instance pure_ibi_sepalg.
Local Existing Instance pureop_pure_ibi_sepalg.
Local Existing Instance pure_ibi_embed_drop.
Local Existing Instance PureBILPre.
Local Existing Instance PureBILPreOp.
Local Existing Instance PureBILFun.
Local Existing Instance PureBILFunOp.

(* Set Printing All. *)
Print pureop_bi_sepalg.

Local Instance PureOpAsn1 : @PureOp asn1 := _.
Local Instance PureAsn1 : Pure PureOpAsn1 := _.
Local Instance PureOpAsn2 : @PureOp asn2 := _.
Local Instance PureAsn2 : Pure PureOpAsn2 := _.
Local Instance PureOpAsn : @PureOp asn := _.
Local Instance PureAsn : Pure PureOpAsn := _.
Local Instance PureOpSasn : @PureOp sasn := _.
Local Instance PureSAsn : Pure PureOpSasn := _.

Instance pure_prop (p : Prop) : pure (@embed Prop sasn _ p) := _.
Instance pure_vlogic (p : vlogic) : pure (@embed vlogic sasn _ p) := _.
Instance pure_spec_asn (p : spec) : pure (@embed spec asn _ p) := _.
Instance pure_spec (p : spec) : pure (@embed spec sasn _ p) := _.

Local Transparent ILPre_Ops.

Definition mk_asn (f: Prog_wf -> nat -> heap -> Prop)
  (Hnat: forall P k h, f P (S k) h -> f P k h)
  (HProg: forall P P' k h, Prog_wf_sub P P' -> f P k h -> f P' k h)
  (Hheap: forall P k h h', subheap h h' -> f P k h -> f P k h') : asn.
  refine (mkILPreFrm (fun P => mkILPreFrm (fun k => mkILPreFrm (fun h => f P k h) _) _) _).
Proof.
  intros P P' HP Hn h H; simpl.
  eapply HProg; eassumption.
Grab Existential Variables.
  assert (forall k' k P h, k' >= k -> f P k' h -> f P k h) as Hnat'.
  intros k k' P' h Hkk' S.  
  induction Hkk'. assumption.
  apply IHHkk'. apply Hnat. assumption.
  intros n n' Hn'' p S; simpl in *. eapply Hnat'; eassumption.
  intros h h' Hh H. eapply Hheap; eassumption.
Defined.

Program Definition pointsto_aux (x : ptr) (f : field) (v : val) : asn :=
  mk_asn (fun P k h => subheap ((empty val) [(x, f) <- v]) (get_heap_ptr h)) _ _ _.
Next Obligation.
  destruct h, h'; simpl in *.
  apply subheap_prod in H as [H _].
  setoid_rewrite H in H0. assumption.
Qed.

Definition pointsto (p : val) (f : field) (v : val) : asn :=
  (p <> null) /\\ pointsto_aux (val_to_ptr p) f v.

Program Definition pointsto_arr_element_aux (x : val) (path : list val) (v : val) : asn :=
  mk_asn (fun P k h => exists (h' : heap) , 
                         subheap h' h /\
                         find_heap_arr (val_to_nat x)
                                       (List.map val_to_nat path) (get_heap_arr h') = 
                         Some v) _ _ _.
Next Obligation.
  exists H; split; [assumption | reflexivity].
Qed.
Next Obligation.
  exists H0; split; [assumption | reflexivity].
Qed.
Next Obligation.
  exists H0; split; [etransitivity; eassumption | reflexivity].
Qed.

Definition pointsto_arr_element (x i : val) (v : val) : asn := 
  pointsto_arr_element_aux x (i::nil) v.

Require Import ZArith.

Fixpoint pointsto_arr_aux (x : val) (n : nat) (vs : list val) : asn :=
  match vs with
    | nil   => empSP
    | v::vs => pointsto_arr_element x (vint (Z_of_nat n)) v ** 
                                    pointsto_arr_aux x (S n) vs
  end.

Opaque ILogicOpsAsn.

Lemma firstn_nil {A : Type} (n : nat) : firstn n (@nil A) = nil.
Proof.
  destruct n; simpl; reflexivity.
Qed.

Lemma skipn_nil {A : Type} (n : nat) : skipn n (@nil A) = nil.
Proof.
  destruct n; simpl; reflexivity.
Qed.

Lemma firstn_cons {A : Type} (n : nat) (x : A) (xs : list A) (H : n > 0) :
  firstn n (x :: xs) = x :: (firstn (n - 1) xs).
Proof.
  destruct n; simpl.
  + omega.
  + replace (n - 0) with n by omega; reflexivity.
Qed.

Lemma firstn_app1 {A : Type} (n : nat) (xs ys : list A) (H : n <= List.length xs) :
  firstn n (xs ++ ys) = firstn n xs.
Proof.
  generalize dependent n; induction xs; simpl in *; intros.
  + assert (n = 0) by omega; clear H; subst; simpl; reflexivity.
  + destruct n; simpl in *; [reflexivity|].
    f_equal. apply IHxs. omega.
Qed.
  
Lemma firstn_app2 {A : Type} (n : nat) (xs ys : list A) (H : n >= List.length xs) :
  firstn n (xs ++ ys) = xs++(firstn (n - List.length xs) ys).
Proof.
  generalize dependent n; induction xs; simpl in *; intros.
  + replace (n - 0) with n by omega; reflexivity.
  + destruct n; simpl in *; [omega|].
    f_equal. apply IHxs. omega.
Qed.
  
Lemma skipn_cons {A : Type} (n : nat) (x : A) (xs : list A) (H : n > 0) :
  skipn n (x :: xs) = skipn (n - 1) xs.
Proof.
  destruct n; simpl.
  + omega.
  + replace (n - 0) with n by omega; reflexivity.
Qed.

Lemma skipn_drop {A : Type} (n : nat) (xs : list A) (H : n >= List.length xs) :
  skipn n xs = nil.
Proof.
  generalize dependent xs; induction n; simpl; intros.
  + destruct xs; simpl in *; [reflexivity | omega].
  + destruct xs; [reflexivity|].
    apply IHn; simpl in *; omega.
Qed.

Lemma skipn_length {A : Type} (n : nat) (vs : list A) :
  List.length (skipn n vs) = (List.length vs - n).
Proof.
  generalize dependent n; induction vs; simpl.
  + destruct n; simpl; reflexivity.
  + destruct n; simpl; [reflexivity|].
    rewrite IHvs. reflexivity.
Qed.
      


Lemma pointsto_arr_aux_app (x : val) (n : nat) (xs ys : list val) :
  pointsto_arr_aux x n (xs++ys) -|- pointsto_arr_aux x n xs ** pointsto_arr_aux x (n + List.length xs) ys.
Proof.
  generalize dependent n; induction xs; simpl in *; intros.
  + rewrite sepSPC, empSPR. replace (n + 0) with n by omega. reflexivity.
  + rewrite IHxs. 
    replace (n + S (Datatypes.length xs)) with (S n + Datatypes.length xs) by omega.
    rewrite sepSPA. reflexivity.
Qed.

Lemma pointsto_arr_aux_split (x : val) (n m : nat) (vs : list val) (H : n < m) :
  pointsto_arr_aux x n vs -|- pointsto_arr_aux x n (firstn (m - n) vs) **
                              pointsto_arr_aux x m (skipn (m - n) vs).
Proof.
  rewrite <- (firstn_skipn (m - n) vs) at 1.
  rewrite pointsto_arr_aux_app.
  rewrite firstn_length.
  destruct (Min.min_dec (m - n) (Datatypes.length vs)) as [H1 | H1]; rewrite H1.
  + replace (n + (m - n)) with m by omega; reflexivity.
  + rewrite skipn_drop; simpl; [reflexivity|].
    setoid_rewrite <- H1.
    assert (min (m - n) (Datatypes.length vs) <= m - n); [|omega].
    apply Min.le_min_l.
Qed.

Definition pointsto_arr (x n m : val) (vs : list val) : asn :=
  let n' := val_to_nat n in
  let m' := val_to_nat m in
  (n' <= m' /\ List.length vs = S (m' - n')) /\\ pointsto_arr_aux x n' vs.

(* Gregory should be able to pull this off with his cancellation magic. *)

Lemma embed_and_admit (p q : asn) (P Q : Prop) : 
  (P /\\ p) ** (Q /\\ q) -|- P /\\ Q /\\ p ** q.
Proof.
  admit.
Qed.


Lemma pointsto_arr_split (x i j k : val) (vs : list val) 
      (Hij : val_to_nat i <= val_to_nat j) 
      (Hjk : val_to_nat j < val_to_nat k) :
  pointsto_arr x i k vs -|- pointsto_arr x i j (firstn (S ((val_to_nat j) - 
                                                           (val_to_nat i))) vs) ** 
                            pointsto_arr x (vint (Z_of_nat (S (val_to_nat j)))) k 
                                         (skipn (S ((val_to_nat j) - (val_to_nat i))) vs).
Proof.
  unfold pointsto_arr.
   replace (val_to_nat (Z.of_nat (S (val_to_nat j)))) with (S (val_to_nat j)) by
    (destruct j; unfold val_to_nat; simpl in *; try reflexivity;
     rewrite SuccNat2Pos.id_succ; reflexivity).
   split.
  + apply lpropandL; intros [H1 H2].
    rewrite embed_and_admit.
    apply lpropandR. {
      split; [assumption|].
      rewrite firstn_length.
      simpl. setoid_rewrite H2.
      f_equal; apply Min.min_l; omega.
    }
    apply lpropandR. {
      split; [omega|].
      rewrite skipn_length; omega.
    }
    rewrite (pointsto_arr_aux_split x (val_to_nat i) (S(val_to_nat j))); [|omega].
    replace (S (val_to_nat j) - val_to_nat i) with (S (val_to_nat j - val_to_nat i)) by omega.
    reflexivity.

  + rewrite embed_and_admit.
    apply lpropandL; intros [H1 H2].
    apply lpropandL; intros [H3 H4].
    apply lpropandR. split; [omega|].
    rewrite <- (firstn_skipn (S (val_to_nat j - val_to_nat i)) vs), app_length; omega.
    etransitivity; [|rewrite (pointsto_arr_aux_split x (val_to_nat i) (S(val_to_nat j))); [|omega]]; [|reflexivity]. 
    replace (S (val_to_nat j) - val_to_nat i) with (S (val_to_nat j - val_to_nat i)) by omega.
    reflexivity.
Qed.

Transparent ILogicOpsAsn.
Transparent BILOperatorsAsn.
Transparent BILPre_Ops.
Transparent EmbedAsnPropOp.
Transparent EmbedILPreDropOp.
Opaque MapSepAlgOps.
Opaque SepAlgOps_prod.

Lemma pointsto_arr_pointsto_element_lst (x i : val) (vs : list val) :
  pointsto_arr x i i vs |-- Exists v, vs = v::nil /\\ pointsto_arr_element x i v.
Proof.
  unfold pointsto_arr, pointsto_arr_element.
  apply lpropandL; intros [H1 H2].
  destruct vs; simpl in H2; [omega|].
  destruct vs; simpl in H2; [|omega].
  cbv [pointsto_arr_aux].
  rewrite empSPR.
  intros P n h H.
  simpl in *.
  destruct H as [h' [Hh H]].
  exists v; split; simpl; [reflexivity|].
  exists h'; split; [assumption|].
  simpl in *.
  assert (val_to_nat (Z.of_nat (val_to_nat i)) = val_to_nat i). {
      clear H.
      induction i; simpl in *; unfold val_to_nat in *; simpl in *; try reflexivity.
      rewrite Nat2Z.id; reflexivity.
    }
  rewrite <- H0. apply H.
Qed.

Lemma pointsto_arr_pointsto_element (x i : val) (v : val) :
  pointsto_arr x i i (v::nil) -|- pointsto_arr_element x i v.
Proof.
  split.
  + rewrite pointsto_arr_pointsto_element_lst.
    apply lexistsL; intro v'.
    apply lpropandL; intros H; inversion H; subst; clear H.
    reflexivity.
  + unfold pointsto_arr_element, pointsto_arr.
    apply lpropandR; [split; [reflexivity | simpl; omega]|].
    cbv [pointsto_arr_aux]. rewrite empSPR.
    intros P n h H; simpl in *.
    destruct H as [h' [Hh H]].
    exists h'; split; [apply Hh|].
    assert (val_to_nat (Z.of_nat (val_to_nat i)) = val_to_nat i). {
      clear H.
      induction i; simpl in *; unfold val_to_nat in *; simpl in *; try reflexivity.
      rewrite Nat2Z.id; reflexivity.
    }
    rewrite H0. apply H.
Qed.

Definition update {A : Type} (lst : list A) (n : nat) (p : A) :=
  firstn n lst ++ (p::(skipn (n+1) lst)).
(*
Lemma pointsto_arr_update (x i j k : val) (vs : list val) (v : val) 
      (Hij : val_to_nat i <= val_to_nat j) 
      (Hjk : val_to_nat j < val_to_nat k) :
  pointsto_arr x i k (update vs (val_to_nat j - val_to_nat i) v) -|- 
  pointsto_arr x i j (firstn ((val_to_nat j) - 
                              (val_to_nat i)) vs) ** 
  pointsto_arr_element k j v **
  pointsto_arr x (vint (Z_of_nat (S (val_to_nat j)))) k 
  (skipn (S ((val_to_nat j) - (val_to_nat i))) vs).
Proof.
  rewrite pointsto_arr_split with (j := S (val_to_nat j)). try eassumption.
  unfold update.
  replace (firstn (val_to_nat j - val_to_nat i) vs ++
                  v :: skipn (val_to_nat j - val_to_nat i + 1) vs) with
  ((firstn (val_to_nat j - val_to_nat i) vs ++
         (v::nil)) ++ (skipn (val_to_nat j - val_to_nat i + 1) vs)) 
    by (rewrite <- app_assoc; reflexivity).
  rewrite firstn_app1.
  rewrite firstn_app2.
  replace (S (val_to_nat j - val_to_nat i) -
         Datatypes.length (firstn (val_to_nat j - val_to_nat i) vs)) with 1.
  replace (firstn 1 (v :: nil)) with (v :: nil) by reflexivity.
  cbv delta [firstn].
SearchAbout firstn.
  simpl.
Qed.
*)
(*

Lemma pointsto_arr_get_element x i j k vs
      (Hij : val_to_nat i <= val_to_nat j)
      (Hjk : val_to_nat j <= val_to_nat k) :
      pointsto_arr x i k vs |-- pointsto_arr_element x j 
                                (List.nth (val_to_nat j - val_to_nat i) vs null).
Proof.
  unfold pointsto_arr.
  apply lpropandL; intros [H1 H2].
  unfold pointsto_arr_element.
  intros p n h; simpl; intros.
  generalize dependent (val_to_nat i).
  generalize dependent (val_to_nat j).
  generalize dependent (val_to_nat k).
  clear i j k.
  intros k j Hjk i Hij Hik Hlength H.
  destruct h as [hp ha].
  exists (hp, heap_arr_unit [(val_to_nat x, j) <- nth (j - i) vs null]).
  split; simpl; [|rewrite add_eq_o; reflexivity].
  apply subheap_prod; split; [reflexivity|].
  generalize dependent k; induction vs; simpl in *; intros. omega.
  inversion Hlength; clear Hlength.
  unfold sepSP in H. unfold BILOperatorsAsn in H.
  simpl in H.
  destruct H as [h1 [h2 [Hh [[h3 [H2 H3]] H4]]]].
  destruct h1, h2, h3.
  apply subheap_prod in H2 as [H2 H5].
  simpl in *.
  remember (j - i) as l; destruct l; simpl in *.
  assert (i = j) by omega; subst.
  admit.
  admit.
Qed.


Fixpoint arr_heap (h : heap_arr) (x : nat) (path indexes : list nat) (v : val) : heap_arr :=
	match path, indexes with
		| nil, i::indexes     => h [(x, i) <- v]
		| n::path, i::indexes => (arr_heap h n path indexes v) [(x, i) <- (varr n)]
		| _, _                => empty val
	end.

Program Definition in_arr_aux (p : val) (path : list nat) (indexes : list val) (v : val) : asn :=
	mk_asn (fun P k h => subheap (arr_heap (empty val) (val_to_arr p) path 
                                               (List.map val_to_arr indexes) v) (snd h)) _ _ _.
Next Obligation.
	destruct h as [_h h]; destruct h' as [_h' h']; simpl in *.
	apply subheap_prod in H as [_ H]; clear _h _h'.
	rewrite H in H0. assumption.
Qed.

Definition in_arr (p : val) (indexes : list val) (v : val) : asn :=
	Exists path : list nat, in_arr_aux p path indexes v.

Fixpoint alloc_arr_val (h : heap_arr) (x size : nat) (f : nat -> val) : heap_arr :=
	match size with
		| 0   => h [(x, 0) <- (f x)]
		| S n => (alloc_arr_val h x n f) [(x, S n) <- null]
	end.

Fixpoint alloc_arr_aux (h : heap_arr) (x : nat) (size : list nat) 
         (paths : list (list nat)) : heap_arr :=
	match size, paths with
		| s::nil, nil            => alloc_arr_val h x s (fun x => null)
		| s :: size, ps :: paths => List.fold_right (fun n h => h [(x, s) <- (varr n)]) h ps
		| _, _                   => empty val
	end.
	
Definition alloc_arr (x : nat) (size : list nat) (paths : list (list nat)) : heap_arr :=
	alloc_arr_aux (empty val) x size paths.
*)	