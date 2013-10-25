Require Import List String RelationClasses Morphisms Setoid.
Require Import Lang Util.

Set Implicit Arguments.
Unset Strict Implicit.

Program Fixpoint search_NoDup
    {A} (A_dec: forall a b: A, {a=b}+{a<>b}) (l: list A) : option (NoDup l) :=
  match l with
  | nil => Some _
  | a::l' =>
      match search_NoDup A_dec l' with
      | Some nodup =>
          match In_dec A_dec a l' with
          | left isin => None
          | right notin => Some _
          end
      | None => None
      end
  end.
Next Obligation.
intros. constructor.
Qed. Next Obligation.
intros. subst. constructor; assumption.
Defined.

Record Method := {
  m_params: list var;
  m_body: cmd;
  m_ret: dexpr
}.

Record Class := {
  c_fields  : SS.t;
  c_methods : SM.t Method
}.

Record Program := {
  p_classes: SM.t Class
}.

Section Pwf.

  Variable Prog: Program.

  Definition field_lookup (C:class) (fields:SS.t) :=
    exists Crec, SM.MapsTo C Crec (p_classes Prog) /\
      fields = c_fields Crec.

  Lemma field_lookup_function: forall C f f',
    field_lookup C f -> field_lookup C f' -> f = f'.
  Proof.
    unfold field_lookup.
    intros C f f' HM1 HM2. destruct HM1 as [m HM1]. destruct HM2 as [m' HM2].
    assert (m = m') by firstorder using SM'.MapsTo_fun. intuition congruence.
  Qed.

  Definition method_lookup (C:class) m mrec :=
    exists Crec, SM.MapsTo C Crec (p_classes Prog) /\
      SM.MapsTo m mrec (c_methods Crec).

  Lemma method_lookup_function : forall C m mr0 mr1
    (HML0 : method_lookup C m mr0)
    (HML1 : method_lookup C m mr1),
    mr0 = mr1.
  Proof.
    unfold Pwf.method_lookup; intros; destruct HML0 as [C0 [HC0 HM0]];
      destruct HML1 as [C1 [HC1 HM1]].
    rewrite SM'.find_mapsto_iff in *; rewrite HC0 in HC1; inversion HC1; subst.
    rewrite HM0 in HM1; inversion HM1; subst; reflexivity.
  Qed.

  Program Definition search_method_lookup
      {P': method -> Method -> Prop} (search: forall m mrec, option (P' m mrec))
      : option (forall C m mrec, method_lookup C m mrec -> P' m mrec) :=
    search_cast _ _ (
      SM'.search_forall (fun _ Crec =>
        SM'.search_forall (fun m mrec =>
          search m mrec
        ) (c_methods Crec)
      ) (p_classes Prog)
    ).
  Next Obligation.
    firstorder.
  Qed.

  Program Definition search_method_class_lookup
    {P' : class -> method -> Method -> Prop}
    (search: forall C m mrec, option (P' C m mrec)) : option (
      forall C m mrec, method_lookup C m mrec -> P' C m mrec) :=
      search_cast _ _ (
        SM'.search_forall (fun C Crec =>
          SM'.search_forall (fun m mrec =>
            search C m mrec) (c_methods Crec)) (p_classes Prog)).
  Next Obligation.
    firstorder.
  Qed.

Definition search_unique_names : option (
      forall C m mrec,
      method_lookup C m mrec ->
      NoDup (m_params mrec)) :=
  search_method_class_lookup (fun _ _ mrec =>
    search_NoDup string_dec (m_params mrec)
  ).

End Pwf.

Definition lift_option_rel (T : Type) (R : relation T) : relation (option T) :=
  fun x y => match x, y with
               | Some x, Some y => R x y
               | None, None => True
               | _, _ => False
             end.

Infix "=^=" := (lift_option_rel equiv) (at level 70, no associativity).

Instance opt_eq_rel T (R : relation T) {Eq : Equivalence R} : Equivalence (lift_option_rel R).
Proof.
  destruct Eq as [RR RS RT]; split.
  intros [x |]; simpl; intuition.
  intros [x |] [y |]; simpl; intuition.
  intros [x |] [y |] [z |]; simpl; intuition eauto.
Qed.

Definition Prog_compat (P Q : Program) :=
  forall C, ~ (SM.In C (p_classes P) /\ SM.In C (p_classes Q)).

Definition Prog_sub (P Q : Program) :=
  forall C crec, SM.find C (p_classes P) = Some crec ->
    exists crec', SM.find C (p_classes Q) = Some crec' /\
      SS.Equal (c_fields crec) (c_fields crec') /\
      SM.Equal (c_methods crec) (c_methods crec').

Definition optAddClass C crec oP : option Program :=
  match oP with
    | Some P => match SM.find C (p_classes P) with
                  | Some _ => None
                  | None   => Some (Build_Program (SM.add C crec (p_classes P)))
                end
    | None   => None
  end.
Definition Prog_comp (P Q : Program) := SM.fold optAddClass (p_classes P) (Some Q).
Definition crec_eq (C D : Class) := SS.Equal (c_fields C) (c_fields D) /\ SM.Equal (c_methods C) (c_methods D).
Definition Prog_eq (P Q : Program) :=
  forall C, lift_option_rel crec_eq (SM.find C (p_classes P)) (SM.find C (p_classes Q)).

Instance crec_eq_Equiv : Equivalence crec_eq.
Proof.
  split.
  + intros P; split; reflexivity.
  + intros P Q [HF HM]; split; symmetry; assumption.
  + intros P Q R [HFPQ HMPQ] [HFQR HMQR]; split; etransitivity; eassumption.
Qed.

Instance Prog_eq_Equiv : Equivalence Prog_eq.
Proof.
  split.
  + intros P C. reflexivity.
  + intros P Q HPQ C; symmetry; apply HPQ.
  + intros P Q R HPQ HQR C; etransitivity; revert C; eassumption.
Qed.

Definition uniq_params Prog := forall C m mrec, method_lookup Prog C m mrec -> NoDup (m_params mrec).
Record Prog_wf := { program :> Program; prog_wf : uniq_params program}.

Lemma SM'Empty_not_in : forall {elt} S, SM.Empty (elt := elt) S <-> (forall C, ~ SM.In C S).
Proof.
  split; intros.
  + rewrite SM'.not_find_in_iff; destruct (SM.find C S) as [D |] eqn: Heq;
    [rewrite <- SM'.find_mapsto_iff in Heq; contradiction (H _ _ Heq) | reflexivity].
  + intros C v HMT; apply SM'.find_mapsto_iff in HMT; apply (H C); rewrite SM'.in_find_iff; congruence.
Qed.

Instance optAddClass_m : Proper (eq ==> eq ==> lift_option_rel Prog_eq ==> lift_option_rel Prog_eq) optAddClass.
Proof.
  intros D C Hdc d c HDC [P |] [Q |] HPQ; subst; simpl in *; try (contradiction || exact I); []; assert (HC := HPQ C).
  destruct (SM.find C (p_classes P)) as [cP |] eqn: EQP; destruct (SM.find C (p_classes Q)) as [cQ |] eqn: EQQ;
    try (contradiction || reflexivity); simpl; [].
  intros D; simpl; rewrite !SM'.add_o; destruct (SM'.eq_dec C D); simpl; [reflexivity | apply HPQ].
Qed.

Lemma optAddClass_trneqk : SM'.transpose_neqkey (lift_option_rel Prog_eq) optAddClass.
Proof.
  intros x y C D [P |] NEQ; simpl; [| exact I].
  destruct (SM.find y (p_classes P)) as [cyP |] eqn: EQyP; destruct (SM.find x (p_classes P)) as [cxP |] eqn: EQxP; simpl;
    [exact I |..]; rewrite !SM'.add_neq_o, ?EQxP, ?EQyP; try congruence; simpl; try exact I; [].
  intros z; simpl; rewrite !SM'.add_o; destruct (SM'.eq_dec x z); destruct (SM'.eq_dec y z); subst; congruence || reflexivity.
Qed.
Hint Resolve optAddClass_trneqk : program.

Lemma Prog_comp_in x P Q (InPQ : match Prog_comp P Q with Some R => SM.In x (p_classes R) | None => False end) :
  SM.In x (p_classes P) \/ SM.In x (p_classes Q).
Proof.
  destruct P as [P]; induction P using SM'.map_induction; unfold Prog_comp in *; simpl in *.
  { right; destruct (SM.fold optAddClass P (Some Q)) as [R |] eqn: EQ; [| contradiction].
    assert (HEQ : lift_option_rel Prog_eq (SM.fold optAddClass P (Some Q)) (Some R)) by (rewrite EQ; reflexivity).
    rewrite SM'.fold_Empty with (eqA := lift_option_rel Prog_eq) in HEQ; auto with typeclass_instances.
    specialize (HEQ x); rewrite SM'.in_find_iff in *; destruct (SM.find x (p_classes R)); [| congruence].
    destruct (SM.find x (p_classes Q)); [congruence | contradiction].
  }
  destruct (SM.fold optAddClass P2 (Some Q)) as [R |] eqn: EQ; [| contradiction].  
  assert (HEQ : lift_option_rel Prog_eq (SM.fold optAddClass P2 (Some Q)) (Some R)) by (rewrite EQ; reflexivity); clear EQ.
  rewrite SM'.fold_Add with (eqA := lift_option_rel Prog_eq) in HEQ; eauto with typeclass_instances program.
  destruct (SM.fold optAddClass P1 (Some Q)) as [S |] eqn: EQ; [| contradiction].
  assert (HEQS : lift_option_rel Prog_eq (SM.fold optAddClass P1 (Some Q)) (Some S)) by (rewrite EQ; reflexivity).
  simpl in *. destruct (SM.find x0 (p_classes S)) as [] eqn: EQx0; [contradiction |]; specialize (HEQ x); simpl in *.
  rewrite SM'.in_find_iff, H0, SM'.add_o; rewrite SM'.add_o in HEQ; destruct (SM'.eq_dec x0 x); [subst; left; congruence |].
  rewrite <- SM'.in_find_iff; apply IHP1; clear -InPQ HEQ n; rewrite SM'.in_find_iff in *; simpl in *.
  destruct (SM.find x (p_classes S)); [congruence |]; destruct (SM.find x (p_classes R)); [contradiction | congruence].
Qed.

Lemma in_Prog_comp x P Q (INQ : SM.In x (p_classes Q)) : match Prog_comp P Q with Some R => SM.In x (p_classes R) | None => True end.
Proof.
  destruct P as [P]; induction P using SM'.map_induction; unfold Prog_comp in *; simpl in *.
  { destruct (SM.fold optAddClass P (Some Q)) as [R |] eqn: EQ; [| exact I].
    assert (EQR : lift_option_rel Prog_eq (SM.fold optAddClass P (Some Q)) (Some R)) by (rewrite EQ; reflexivity); clear EQ.
    rewrite SM'.fold_Empty with (eqA := lift_option_rel Prog_eq) in EQR; auto with typeclass_instances;
      specialize (EQR x); rewrite SM'.in_find_iff in *; simpl in *.
    destruct (SM.find x (p_classes R)); [congruence |]; destruct (SM.find x (p_classes Q)); [contradiction | congruence].
  }
  destruct (SM.fold optAddClass P2 (Some Q)) as [R |] eqn: EQ; [| exact I].
  assert (EQR : lift_option_rel Prog_eq (SM.fold optAddClass P2 (Some Q)) (Some R)) by (rewrite EQ; reflexivity); clear EQ.
  rewrite SM'.fold_Add with (eqA := lift_option_rel Prog_eq) in EQR; eauto with typeclass_instances program.
  destruct (SM.fold optAddClass P1 (Some Q)) as [S |] eqn: EQ; [| contradiction].
  assert (EQS : lift_option_rel Prog_eq (SM.fold optAddClass P1 (Some Q)) (Some S)) by (rewrite EQ; reflexivity); clear EQ.
  simpl in *; destruct (SM.find x0 (p_classes S)) as [v |] eqn: HEQ; [contradiction |]; specialize (EQR x); simpl in *.
  rewrite SM'.in_find_iff in *; destruct (SM.find x (p_classes R)); [congruence |].
  rewrite SM'.add_o in EQR; destruct (SM'.eq_dec x0 x); [contradiction |].
  destruct (SM.find x (p_classes S)); [contradiction | congruence].
Qed.
  
Lemma Prog_compat_comp : forall P Q, Prog_compat P Q <-> exists R, lift_option_rel Prog_eq (Prog_comp P Q) (Some R).
Proof.
  intros [P] Q; induction P using SM'.map_induction; split; intros.
  + unfold Prog_comp; simpl; exists Q; rewrite SM'.fold_Empty; auto with typeclass_instances; reflexivity.
  + rewrite SM'Empty_not_in in H; intros C [HF _]; simpl in HF; contradiction (H _ HF).
  + { destruct (proj1 IHP1) as [R HR].
    * intros C [HInP1 HInQ]; contradiction (H1 C); split; [| assumption]; simpl in *; rewrite SM'.in_find_iff in *.
      rewrite H0, SM'.add_neq_o; [assumption | intros EQ; subst; contradiction].
    * destruct (optAddClass x e (Some R)) as [S |] eqn: HS.
      exists S; unfold Prog_comp; simpl; rewrite <- HS, SM'.fold_Add; eauto with typeclass_instances program; [].
      unfold Prog_comp in HR; simpl in HR; rewrite HR; reflexivity.
    contradiction (H1 x); simpl; split.
    rewrite SM'.in_find_iff, H0, SM'.add_eq_o; congruence.
    destruct (@Prog_comp_in x {| p_classes := P1 |} Q); [| simpl in *; contradiction | assumption].
    destruct (Prog_comp {| p_classes := P1 |} Q) as [S |]; [| contradiction].
      simpl in *; specialize (HR x); rewrite SM'.in_find_iff; destruct (SM.find x (p_classes R)); [| congruence].
      destruct (SM.find x (p_classes S)); [congruence | contradiction].
  }
  + destruct H1 as [R EQ]; intros y [INP INQ]; simpl in *.
  unfold Prog_comp in EQ; rewrite SM'.fold_Add with (eqA := lift_option_rel Prog_eq) in EQ; eauto with typeclass_instances program.
  assert (INS := in_Prog_comp {| p_classes := P1 |} INQ); unfold Prog_comp in INS; simpl in INS.
  destruct (SM.fold optAddClass P1 (Some Q)) as [S |] eqn: EQ1; [| contradiction].
  simpl in *; rewrite SM'.in_find_iff in *; destruct (SM.find x (p_classes S)) as [] eqn: EQx; [contradiction |].
  rewrite H0, SM'.add_o in INP; destruct (SM'.eq_dec x y); [congruence |].
  eapply IHP1; [unfold Prog_comp; simpl; rewrite EQ1; eexists; reflexivity | simpl; rewrite !SM'.in_find_iff; split; eassumption].
Qed.

Instance Prog_sub_preo : PreOrder Prog_sub.
Proof.
  split.
  + intros P x C HF; exists C; repeat split; trivial.
  + intros P Q R HPQ HQR x C HF.
  destruct (HPQ _ _ HF) as [D [HLu [HFs HMs]]].
  destruct (HQR _ _ HLu) as [E [HLuR [HFs' HMs']]].
  exists E; split; [assumption | split; etransitivity; eassumption].
Qed.

Definition Prog_wf_sub (P Q : Prog_wf) := Prog_sub P Q.
Instance Prog_wf_sub_preo : PreOrder Prog_wf_sub.
Proof.
	split.
	+ intros x; unfold Prog_wf_sub. reflexivity.
	+ intros x y z Hxy Hyz; unfold Prog_wf_sub in *; transitivity y; assumption.
Qed.

