Require Import List Coq.Strings.String RelationClasses Morphisms Setoid.
Require Import Lang Util.

Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Tactics.Consider.

Require Import ExtLib.Data.PPair.
Require Import ExtLib.Data.PList.
Require Import ExtLib.Data.String.

Set Implicit Arguments.
Unset Strict Implicit.

Record Method := {
  m_params: plist var;
  m_body: cmd;
  m_ret: dexpr
}.

Instance RelDec_Method : RelDec (@eq Method) := {
	rel_dec m1 m2 := (m_params m1 ?[ eq ] m_params m2 &&
					  m_body m1 ?[ eq ] m_body m2 &&
					  m_ret m1 ?[ eq ] m_ret m2)%bool
}.

Instance RelDec_Correct_Method : RelDec_Correct RelDec_Method.
Proof.
	split; intros; destruct x, y; simpl.
	consider (m_params0 ?[ eq ] m_params1);
	consider (m_body0 ?[ eq ] m_body1);
	consider (m_ret0 ?[ eq ] m_ret1); simpl; intuition congruence.
Qed.

Record Class := {
  c_fields  : plist field;
  c_methods : plist (ppair string Method)
}.

Require Import ExtLib.Data.String.

Definition rel_dec_Class (c1 c2 : Class) : bool :=
  (c_fields c1 ?[ eq ] c_fields c2 && c_methods c1 ?[ eq ] c_methods c2).

Polymorphic Instance RelDec_Class : RelDec (@eq Class) := {
    rel_dec := rel_dec_Class
}.

Instance RelDec_Correct_Class : RelDec_Correct RelDec_Class.
Proof.
  split; intros; destruct x, y; simpl; unfold rel_dec_Class; simpl. 
  consider (c_fields0 ?[ eq ] c_fields1);
    consider (c_methods0 ?[ eq ] c_methods1); intros; subst;
		 simpl; try intuition congruence.
Qed.

Record Program := {
  p_classes: plist (ppair string Class)
}.

Instance RelDec_Program : RelDec (@eq Program) := {
  rel_dec p1 p2 := (p_classes p1) ?[ eq ] (p_classes p2)
}.

Instance RelDec_Correct_Program : RelDec_Correct RelDec_Program.
Proof.
  split; intros; destruct x, y; simpl.
  consider (p_classes0 ?[ eq ] p_classes1); intuition congruence.
Qed.

Definition valid_method (M : Method) := nodup (m_params M).

Definition valid_class (C : Class) : bool :=
  let (names, methods) := split (c_methods C) in
  nodup (c_fields C) && nodup names &&
	allb (fun M => valid_method M) methods.

Definition valid_program (P : Program) : bool :=
  let (names, classes) := split (p_classes P) in
  nodup names && allb valid_class classes.

Fixpoint class_lookup_aux C (lst : plist (ppair string Class)) :=
  match lst with
  | pnil => None
  | pcons (pprod c Crec) ls => if C ?[ eq ] c then Some Crec else class_lookup_aux C ls
  end.

Definition class_lookup C P := class_lookup_aux C (p_classes P).

Fixpoint method_lookup_aux m (lst : plist (ppair string Method)) :=
  match lst with
  | pnil => None
  | pcons (pprod m' M) ls => if m ?[ eq ] m' then Some M else method_lookup_aux m ls
  end.

Definition method_lookup' C M P :=
  match class_lookup C P with 
    | Some Crec => method_lookup_aux M (c_methods Crec)
    | None => None
  end.

Polymorphic Lemma split_Prop {A B C : Type} (lst : plist (ppair A B)) (P : plist A -> plist B -> C) : 
	(let (a, b) := split lst in P a b) =
	P (fst (split lst)) (snd (split lst)).
Proof.
  generalize dependent C.
  induction lst; try reflexivity; intros; destruct t; simpl.
  replace (let (g, d) := split lst in (pcons a g, pcons b d)) with
  		  (pcons a (fst (split lst)), pcons b (snd (split lst))) by (symmetry; apply IHlst).
  reflexivity.
Qed.

Section Pwf.

  Variable Prog: Program.
  Variable (Valid : valid_program Prog = true).

  Definition field_lookup (C:string) (fields: plist field) :=
  	exists Crec, pIn (pprod C Crec) (p_classes Prog) /\
  		fields = c_fields Crec.

  Lemma field_lookup_function C f f' 
  	(H1 : field_lookup C f) (H2 : field_lookup C f') : f = f'. 
  Proof.
    unfold field_lookup in *.
    destruct H1 as [m [H11 H12]]; destruct H2 as [n [H21 H22]].
    unfold valid_program in Valid. simpl in *.
    assert (m = n); [|subst; reflexivity].
    rewrite split_Prop in Valid.
    induction (p_classes Prog); simpl in *; try intuition congruence.
    destruct t; simpl in *.    
    rewrite split_Prop in Valid.
    simpl in *.
    repeat rewrite Bool.andb_true_iff in Valid.
    rewrite Bool.negb_true_iff in Valid.
    destruct Valid as [[H1 H2] H3]; clear Valid.
    destruct H11, H21.
    + inversion H; inversion H0; subst; apply H8.
    + inversion H; subst; clear IHp.
      assert (~inb C (fst (split p)) = true) by (intuition congruence).
      contradiction H4; clear H H4.
      apply inb_complete.
      apply pIn_split_l in H0. apply H0.
    + inversion H0; subst; clear IHp.
      assert (~inb C (fst (split p)) = true) by (intuition congruence).
      contradiction H4.
      apply inb_complete.
      apply pIn_split_l in H. apply H.
    + apply IHp; try assumption.
      rewrite Bool.andb_true_iff. split. assumption.
      destruct (valid_class c); [assumption|congruence].
  Qed.

  Definition method_lookup (C:string) m mrec :=
    exists Crec, pIn (pprod C Crec) (p_classes Prog) /\
      pIn (pprod m mrec) (c_methods Crec).

  Lemma method_lookup_function : forall C m mr0 mr1
    (HML0 : method_lookup C m mr0)
    (HML1 : method_lookup C m mr1),
    mr0 = mr1.
  Proof.
    unfold Pwf.method_lookup; intros; destruct HML0 as [C0 [HC0 HM0]];
      destruct HML1 as [C1 [HC1 HM1]].
    unfold valid_program in Valid. simpl in *.
    rewrite split_Prop, Bool.andb_true_iff in Valid.
    destruct Valid; clear Valid.
    induction (p_classes Prog); simpl in *; try intuition congruence.
    destruct t; simpl in *.
    rewrite split_Prop in H, H0; simpl in *; rewrite Bool.andb_true_iff in H.
    remember (valid_class c). symmetry in Heqb.
    destruct b; [|congruence].
    destruct H.
    rewrite Bool.negb_true_iff in H.
    destruct HC0, HC1.
    + clear IHp; inversion H2; inversion H3. repeat subst; clear H H1 H2 H3 H7.
      unfold valid_class in Heqb. rewrite split_Prop in Heqb; repeat rewrite Bool.andb_true_iff in Heqb.
      destruct Heqb as [[_ H] _].
      induction (c_methods C1); simpl in *; try intuition congruence.
      destruct t; rewrite split_Prop in H; simpl in H.
      rewrite Bool.andb_true_iff in H; destruct H as [H1 H2].
      rewrite Bool.negb_true_iff in H1.
      destruct HM1, HM0.
      * inversion H; inversion H3; repeat subst; reflexivity.
      * inversion H; subst; clear IHp0.
        assert (~inb m (fst (split p0)) = true) by intuition congruence.
        contradiction H4. apply inb_complete.
        apply pIn_split_l in H3; apply H3.
      * inversion H3; subst; clear IHp0.
        assert (~inb m (fst (split p0)) = true) by intuition congruence.
        contradiction H4. apply inb_complete.
        apply pIn_split_l in H; apply H.
      * apply IHp0; assumption.
    + inversion H2; subst; clear IHp.
      assert (~inb C (fst (split p)) = true) by (intuition congruence).
      contradiction H4; clear H H4.
      apply inb_complete.
      apply pIn_split_l in H3. apply H3.
    + inversion H3; subst; clear IHp.
      assert (~inb C (fst (split p)) = true) by (unfold class; intuition congruence).
      contradiction H4; clear H H4.
      apply inb_complete.
      apply pIn_split_l in H2. apply H2.
    + apply IHp; try assumption.
  Qed.

  Lemma method_lookup_nodup C m mr (H : method_lookup C m mr) : pNoDup (m_params mr).
  Proof.
    unfold method_lookup in H.
    destruct H as [Crec [H1 H2]].
    unfold valid_program in Valid.
    rewrite split_Prop, Bool.andb_true_iff in Valid.
    destruct Valid as [H3 H4]; clear Valid.
    induction (p_classes Prog); simpl in *; try intuition congruence.
    destruct t; rewrite split_Prop in H3; simpl in *.
    rewrite Bool.andb_true_iff in H3; destruct H3 as [H3 H5].
    rewrite Bool.negb_true_iff in H3.
    rewrite split_Prop in H4; simpl in *.
    remember (valid_class c) as b; destruct b; symmetry in Heqb; [|congruence].
    unfold valid_class in Heqb. rewrite split_Prop in Heqb; repeat rewrite Bool.andb_true_iff in Heqb.
    destruct Heqb as [[H6 _] H7].
    destruct H1 as [H1 | H1]; [
	inversion H1; repeat subst; clear H1 IHp|
	apply IHp; assumption
      ].
    clear H3 H4 H5 H6 p C Prog.
    induction (c_methods Crec); simpl in *; try intuition congruence.
    destruct t; simpl in *; rewrite split_Prop in H7; simpl in *.
    remember (valid_method m0) as b; destruct b; [|congruence]; symmetry in Heqb.
    destruct H2 as [H2 | H2]; [|apply IHp; assumption].
    inversion H2; subst; clear H2 H7 IHp.
    unfold valid_method in Heqb. apply nodup_sound; assumption.
  Qed.

End Pwf.

Definition Prog_compat (P Q : Program) :=
  forall C, ~ (pIn C (p_classes P) /\ pIn C (p_classes Q)).

Definition Prog_sub (P Q : Program) :=
  forall C crec, pIn (pprod C crec) (p_classes P) ->
    exists crec', pIn (pprod C crec') (p_classes Q) /\
      c_fields crec = c_fields crec' /\
      c_methods crec = c_methods crec'.

Instance Prog_sub_preo : PreOrder Prog_sub.
Proof.
  split.
  + intros P x C HF; exists C; repeat split; trivial.
  + intros P Q R HPQ HQR x C HF.
  destruct (HPQ _ _ HF) as [D [HLu [HFs HMs]]].
  destruct (HQR _ _ HLu) as [E [HLuR [HFs' HMs']]].
  exists E; split; [assumption | split; etransitivity; eassumption].
Qed.
