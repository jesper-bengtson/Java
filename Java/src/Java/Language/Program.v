Require Import List Coq.Strings.String RelationClasses Morphisms Setoid.
Require Import Lang Util.

Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Tactics.Consider.

Require Import ExtLib.Data.Pair.
Require Import ExtLib.Data.PList.

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
  c_fields  : list field;
  c_methods : list (string * Method)
}.

Instance RelDec_Class : RelDec (@eq Class) := {
	rel_dec c1 c2 := (c_fields c1 ?[ eq ] c_fields c2 &&
					  c_methods c1 ?[ eq ] c_methods c2)%bool
}.

Instance RelDec_Correct_Class : RelDec_Correct RelDec_Class.
Proof.
	split; intros; destruct x, y; simpl.
	consider (c_fields0 ?[ eq ] c_fields1);
	consider (c_methods0 ?[ eq ] c_methods1); intros;
		 simpl; try intuition congruence.
Qed.

Record Program := {
  p_classes: list (string * Class)
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
	List.nodup (c_fields C) && nodup names &&
	  forallb (fun M => valid_method M) methods.

Definition valid_program (P : Program) : bool :=
	let (names, classes) := split (p_classes P) in
	    nodup names &&
		forallb valid_class classes.

Fixpoint class_lookup_aux C (lst : list (string * Class)) :=
	match lst with
		| nil => None
		| (c, Crec)::ls => if C ?[ eq ] c then Some Crec else class_lookup_aux C ls
	end.

Definition class_lookup C P := class_lookup_aux C (p_classes P).

Fixpoint method_lookup_aux m (lst : list (string * Method)) :=
	match lst with
		| nil => None
		| (m', M)::ls => if m ?[ eq ] m' then Some M else method_lookup_aux m ls
	end.

Definition method_lookup' C M P :=
  match class_lookup C P with 
    | Some Crec => method_lookup_aux M (c_methods Crec)
    | None => None
  end.

Lemma split_Prop {A B C : Type} (lst : list (A * B)) (P : list A -> list B -> C) : 
	(let (a, b) := split lst in P a b) =
	P (fst (split lst)) (snd (split lst)).
Proof.
  generalize dependent C.
  induction lst; try reflexivity; intros; destruct a; simpl.
  replace (let (g, d) := split lst in (a :: g, b :: d)) with
  		  (a :: fst (split lst), b :: snd (split lst)) by (symmetry; apply IHlst).
  reflexivity.
Qed.

Section Pwf.

  Variable Prog: Program.
  Variable (Valid : valid_program Prog = true).

  Definition field_lookup (C:class) (fields: list field) :=
  	exists Crec, In (C, Crec) (p_classes Prog) /\
  		fields = c_fields Crec.

  Lemma field_lookup_function C f f' 
  	(H1 : field_lookup C f) (H2 : field_lookup C f') : f = f'. 
  Proof.
    unfold field_lookup in *.
    destruct H1 as [m [H11 H12]]; destruct H2 as [n [H21 H22]].
    unfold valid_program in Valid. simpl in *.
    assert (m = n); [|subst; reflexivity].
    rewrite split_Prop, andb_true_iff in Valid.
    destruct Valid; clear Valid.
    induction (p_classes Prog); simpl in *; try intuition congruence.
    destruct a; simpl in *.
    rewrite split_Prop in H, H0; simpl in *; rewrite andb_true_iff in H, H0.
    destruct H, H0.
    rewrite negb_true_iff in H.
    destruct H11, H21.
    + inversion H3; inversion H4; subst; apply H9.
    + inversion H3; subst; clear IHl.
      assert (~inb C (fst (split l)) = true) by (unfold class; intuition congruence).
	  contradiction H5; clear H H5.
	  apply inb_complete.
	  apply in_split_l in H4. apply H4.
	+ inversion H4; subst; clear IHl.
      assert (~inb C (fst (split l)) = true) by (unfold class; intuition congruence).
	  contradiction H5; clear H H5.
	  apply inb_complete.
	  apply in_split_l in H3. apply H3.
    + apply IHl; try assumption.
  Qed.

  Definition method_lookup (C:class) m mrec :=
    exists Crec, In (C, Crec) (p_classes Prog) /\
      In (m, mrec) (c_methods Crec).

  Lemma method_lookup_function : forall C m mr0 mr1
    (HML0 : method_lookup C m mr0)
    (HML1 : method_lookup C m mr1),
    mr0 = mr1.
  Proof.
    unfold Pwf.method_lookup; intros; destruct HML0 as [C0 [HC0 HM0]];
      destruct HML1 as [C1 [HC1 HM1]].
   unfold valid_program in Valid. simpl in *.
    rewrite split_Prop, andb_true_iff in Valid.
    destruct Valid; clear Valid.
    induction (p_classes Prog); simpl in *; try intuition congruence.
    destruct a; simpl in *.
    rewrite split_Prop in H, H0; simpl in *; rewrite andb_true_iff in H, H0.
    destruct H, H0.
    rewrite negb_true_iff in H.
    destruct HC0, HC1.
    + clear IHl; inversion H3; inversion H4. repeat subst; clear H H1 H2 H3 H4 H8.
	  unfold valid_class in H0. rewrite split_Prop in H0; repeat rewrite andb_true_iff in H0.
	  destruct H0 as [[_ H] _].
	  induction (c_methods C1); simpl in *; try intuition congruence.
	  destruct a; rewrite split_Prop in H; simpl in H.
	  rewrite andb_true_iff in H; destruct H as [H1 H2].
	  rewrite negb_true_iff in H1.
	  destruct HM1, HM0.
	  * inversion H; inversion H0; repeat subst; reflexivity.
	  * inversion H; subst; clear IHl0.
        assert (~inb m (fst (split l0)) = true) by intuition congruence.
        contradiction H3. apply inb_complete.
        apply in_split_l in H0; apply H0.
	  * inversion H0; subst; clear IHl0.
        assert (~inb m (fst (split l0)) = true) by intuition congruence.
        contradiction H3. apply inb_complete.
        apply in_split_l in H; apply H.
	  * apply IHl0; assumption.
    + inversion H3; subst; clear IHl.
      assert (~inb C (fst (split l)) = true) by (unfold class; intuition congruence).
	  contradiction H5; clear H H5.
	  apply inb_complete.
	  apply in_split_l in H4. apply H4.
	+ inversion H4; subst; clear IHl.
      assert (~inb C (fst (split l)) = true) by (unfold class; intuition congruence).
	  contradiction H5; clear H H5.
	  apply inb_complete.
	  apply in_split_l in H3. apply H3.
    + apply IHl; try assumption.
  Qed.

  Lemma method_lookup_nodup C m mr (H : method_lookup C m mr) : NoDup (m_params mr).
  Proof.
    unfold method_lookup in H.
    destruct H as [Crec [H1 H2]].
    unfold valid_program in Valid.
    rewrite split_Prop, andb_true_iff in Valid.
    destruct Valid as [H3 H4]; clear Valid.
	induction (p_classes Prog); simpl in *; try intuition congruence.
	destruct a; rewrite split_Prop in H3; simpl in *.
	rewrite andb_true_iff in H3; destruct H3 as [H3 H5].
	rewrite negb_true_iff in H3.
	rewrite split_Prop in H4; simpl in *.
	rewrite andb_true_iff in H4; destruct H4 as [H4 H6].
	unfold valid_class in H4. rewrite split_Prop in H4; repeat rewrite andb_true_iff in H4.
	destruct H4 as [[H4 _] H7].
	destruct H1 as [H1 | H1]; [
		inversion H1; repeat subst; clear H1 IHl|
		apply IHl; assumption
	].
	clear H3 H4 H5 H6 l C Prog.
	induction (c_methods Crec); simpl in *; try intuition congruence.
	destruct a; simpl in *; rewrite split_Prop in H7; simpl in *.
	rewrite andb_true_iff in H7; destruct H7 as [H1 H3].
	destruct H2 as [H2 | H2]; [|apply IHl; assumption].
	inversion H2; subst; clear H2 H3 IHl.
	unfold valid_method in H1. apply nodup_sound; assumption.
Qed.

End Pwf.

Definition Prog_compat (P Q : Program) :=
  forall C, ~ (In C (p_classes P) /\ In C (p_classes Q)).

Definition Prog_sub (P Q : Program) :=
  forall C crec, In (C, crec) (p_classes P) ->
    exists crec', In (C, crec') (p_classes Q) /\
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
