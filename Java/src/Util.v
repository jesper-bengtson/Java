Require Import DecidableType DecidableTypeEx.
Require Import FSetWeakList FSetFacts FSetProperties.
Require Import FMapWeakList FMapFacts.
Require Import Omega.

Definition search_cast {P': Prop} (P: Prop) (imp: P -> P') (search: option P) : option P' :=
  match search with
    | Some pf => Some (imp pf)
    | None => None
  end.

Lemma opt_dec {A} : forall
  (HDec: forall (e1 e2:A), {e1 = e2} + {e1 <> e2})
  (o1 o2: option A),
  {o1 = o2} + {o1 <> o2}.
Proof.
  decide equality.
Defined.

Module WMapMore_fun (E: UsualDecidableType) (M: FMapInterface.WSfun E).
  Module P := FMapFacts.WProperties_fun E M.
  Include P.F.
  Include P.
  Import M.

  Definition Sub {elt} m m' := forall k (e:elt), MapsTo k e m -> MapsTo k e m'.

  Lemma Sub_reflexive {T}: reflexive _ (@Sub T). Proof. firstorder. Qed.
  Lemma Sub_transitive {T}: transitive _ (@Sub T). Proof. firstorder. Qed.

  Add Parametric Relation T : _ (@Sub T)
    reflexivity proved by Sub_reflexive
    transitivity proved by Sub_transitive
    as Sub_r.

  Add Parametric Morphism A: (@Disjoint A) with signature
    Sub --> Sub --> impl
    as Disjoint_Sub.
  unfold Disjoint. unfold not, impl. intros m1 m1' H1 m2 m2' H2 H k HIn.
  assert (In k m1) by firstorder.
  assert (In k m2) by firstorder.
  firstorder.
  Qed.

  Add Parametric Morphism A: (@In A) with signature
    eq ==> Sub ++> impl
    as In_impl_m.
  Proof. firstorder. Qed.

  Definition singleton {elt} k (e: elt) := add k e (empty elt).

  Lemma singleton_mapsto_iff : forall {elt} k k' (e e': elt),
    MapsTo k e (singleton k' e') <-> k=k' /\ e=e'.
  Proof. intros. unfold singleton. map_iff. intuition. Qed.

  Lemma singleton_in_iff : forall {elt} k k' (e': elt),
    In k (singleton k' e') <-> k=k'.
  Proof. intros. unfold singleton. map_iff. intuition. Qed.

  Lemma Add_in_iff : forall {elt} {k} {v:elt} {m m'}, Add k v m m' -> forall k',
    (In k' m' <-> (In k' m \/ k' = k)).
  Proof.
    unfold Add. intros T k v m m' HAdd k'. split.
    + intros HIn. destruct (eq_dec k' k) as [Heq|Hne].
      * right. assumption.
      * left. specialize (HAdd k'). rewrite add_neq_o in HAdd; [|intuition].
        rewrite in_find_iff in *. congruence.
    + intros [HIn|Heq].
      * specialize (HAdd k'). rewrite in_find_iff in *. rewrite HAdd.
        rewrite add_o. destruct (eq_dec k k'); congruence.
      * subst. specialize (HAdd k). rewrite in_find_iff. rewrite HAdd.
        rewrite add_eq_o; congruence.
  Qed.

(* setoid_rewrite in goal and all hypotheses. *)
Ltac sr lem := try match goal with H : _ |- _ => setoid_rewrite lem in H end;
               try setoid_rewrite lem.
  Ltac simp :=
    repeat progress (
      sr diff_mapsto_iff
    ; sr diff_in_iff
    ; sr empty_mapsto_iff
    ; sr empty_in_iff
    ; sr add_mapsto_iff
    ; sr add_in_iff
    ; sr singleton_mapsto_iff
    ; sr singleton_in_iff
    ).

  Program Definition search_exists_val
    {elt} {P': elt -> Prop} (k : key) (search: forall e, option (P' e))
      (m: t elt) : option (exists e, MapsTo k e m /\ P' e) :=
      match find k m with
        | Some e => if search e then Some _ else None
        | None => None
      end.
  Next Obligation.
    exists e. rewrite find_mapsto_iff; eauto.
  Qed.

  Program Definition search_forall
      {elt} {P': key -> elt -> Prop} (search: forall k e, option (P' k e))
                                     (m: t elt)
      : option (forall k e, MapsTo k e m -> P' k e) :=
    match for_all (fun k e => if search k e then true else false) m with
    | true => Some _
    | false => None
    end.
  Next Obligation.
    symmetry in Heq_anonymous. eapply (proj1 (for_all_iff _ _)) in Heq_anonymous; [|eassumption].
    remember (search k e) as pf'.
    destruct pf' as [pf|]; [auto | discriminate].
  Qed.

  Program Definition search_cond_forall
    {elt} {P': key -> elt -> Prop} {Q: key -> elt -> Prop} 
    (dec: forall k e, {Q k e} + {~(Q k e)})
    (search : forall k e, option (P' k e))
    (m: t elt) : option (forall k e, MapsTo k e m -> Q k e -> P' k e) :=
    search_cast (forall k e, MapsTo k e m -> Q k e -> P' k e) _
    (search_forall (fun k e => match dec k e with
                                 | left pf => match search k e with
                                                | Some pf' => Some _
                                                | None => None
                                              end
                                 | right pf => Some _
                               end) m).
Next Obligation.
intros. contradiction pf.
Qed.

Ltac mapsto_element := constructor; simpl; constructor.

Ltac mapsto_list := 
  match goal with 
    | |- InA _ _ (_::_) =>
      rewrite InA_cons; first [left; mapsto_element | right; mapsto_list]
    | |- InA _ _ (nil) => fail
  end.

Lemma dec_mapsto {elt}: forall 
  (HDec: forall (e1 e2:elt), {e1 = e2} + {e1 <> e2})
  k (e:elt) m,
  (Decidable.decidable (MapsTo k e m)).
Proof.
  unfold Decidable.decidable. intros.
  repeat rewrite find_mapsto_iff.
  destruct (@opt_dec elt HDec (find k m) (Some e)); intuition.
Qed.

Ltac mapsto_tac :=
  match goal with
    | |- MapsTo _ _ _ => rewrite elements_mapsto_iff; simpl; mapsto_list
  end.

End WMapMore_fun.

Module WSetMore_fun (E : UsualDecidableType) (M : FSetInterface.WSfun E).
  Include FSetFacts.WFacts_fun E M.
  Include FSetProperties.WProperties_fun E M.
  Include FSetDecide.WDecide_fun E M.
  Include FSetDecideAuxiliary.

  Import M.

  Lemma In_elements_iff x s :
    In x s <-> List.In x (elements s).
  Proof.
    rewrite elements_iff. rewrite InA_alt. split; [|eauto].
    intros [y [Hy H]]. subst. assumption.
  Qed.

  Program Definition search_forall
      {P': elt -> Prop} (search: forall x, option (P' x)) (s: t)
      : option (forall x, In x s -> P' x) :=
    match for_all (fun x => if search x then true else false) s with
    | true => Some _
    | false => None
    end.
  Next Obligation.
  symmetry in Heq_anonymous. rewrite <- for_all_iff in Heq_anonymous; [|].
  + unfold For_all in Heq_anonymous. specialize (Heq_anonymous _ H).
    remember (search x) as pf'. destruct pf' as [pf|]; [auto | discriminate].
  + intros a b Heq. rewrite Heq. reflexivity.
  Qed.

Lemma diff_ineq: forall s s' s''
  (Hineq: ~ Equal s s')
  (HSub1: Subset s s'')
  (HSub2: Subset s' s''),
  ~ Equal (diff s'' s) (diff s'' s').
Proof.
  intros.
  intro Heq. apply Hineq. clear Hineq. unfold Equal in *. 
  unfold Subset in *. intro x.
  specialize (Heq x). specialize (HSub1 x). specialize (HSub2 x). 
  repeat rewrite diff_iff in Heq. destruct Heq. split.
  + intros. specialize (HSub1 H1). 
    destruct (dec_In x s'). assumption. intuition.
  + intros. specialize (HSub2 H1). 
    destruct (dec_In x s). assumption. intuition.
Qed.

Lemma subset_diff2: forall s s' s''
  (HSub: Subset s s'),
  Subset (diff s'' s') (diff s'' s).
Proof.
  unfold Subset. intros. rewrite diff_iff in *; intuition.
Qed.

Lemma card_diff_le: forall s s',
  cardinal (diff s s') <= cardinal s.
Proof.
  intros.
  assert (Subset (diff s s') s) by apply diff_subset.
  apply subset_cardinal in H. assumption.
Qed.

Lemma subset_cardinal2: forall s' s
  (Hneq: ~ Equal s s')
  (Hsub: Subset s s'),
  cardinal s < cardinal s'.
Proof.
  intro s'. induction s' using set_induction_bis.
  + intros. rewrite <- H in Hneq. rewrite <- H in Hsub. rewrite <- H. intuition.
  + intros. contradict Hneq. unfold Equal. unfold Subset in Hsub.
    intros x. specialize (Hsub x). rewrite empty_iff in *. intuition.
  + intros. 
    destruct (dec_In x s). 
    assert (~ Equal (remove x s) s'). intro Heq. apply Hneq.
    * unfold Equal in Heq. unfold Equal. intro y. specialize (Heq y).
      rewrite add_iff. rewrite remove_iff in Heq.
      destruct Heq as [Hl Hr]. split.
      - intros. destruct (dec_eq x y) as [Heq | Hneq2].
         subst. intuition.
         intuition.
      - intros. destruct H1 as [Heq | HIn].
         subst. intuition.
         intuition congruence.
    * assert (Subset (remove x s) s') as HSub.
      unfold Subset. intros y HIn. 
      rewrite remove_iff in HIn. destruct HIn as [HIn Hneq2]. 
      unfold Subset in Hsub. specialize (Hsub y). rewrite add_iff in Hsub.
      intuition.
    specialize (IHs' _ H1 HSub).
    assert (S (cardinal (remove x s)) < S (cardinal s')) by omega.
    rewrite remove_cardinal_1 in H2; try assumption.
    rewrite add_cardinal_2; assumption.
    * eapply subset_cardinal_lt; try eassumption;
    try (rewrite add_iff; intuition); firstorder.
Qed.

Lemma diff_subset_zero : forall s s'
  (Hcard: cardinal (diff s s') = 0),
  Subset s s'.
Proof.
  intros. rewrite <- cardinal_Empty in Hcard.
  unfold Empty in Hcard. unfold Subset. intros x HIn.
  specialize (Hcard x). rewrite diff_iff in Hcard.
  destruct (dec_In x s'). assumption. intuition.
Qed.

Lemma dec_Empty: forall s, (Decidable.decidable (Empty s)).
Proof.
  unfold Decidable.decidable. intros.
  rewrite is_empty_iff.
  destruct (bool_dec (is_empty s) true); intuition.
Qed.

Lemma dec_Equal: forall s s', (Decidable.decidable (Equal s s')).
Proof.
  intros. unfold Decidable.decidable. rewrite equal_iff.
  destruct (bool_dec (equal s s') true); intuition.
Qed.

End WSetMore_fun.