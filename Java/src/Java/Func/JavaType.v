Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Tactics.

Require Import MirrorCore.TypesI.

Require Import Charge.Views.ILogicView.
Require Import Charge.Views.BILogicView.
Require Import Charge.Views.EmbedView.
Require Import ChargeCore.Open.Subst.
Require Import ChargeCore.Logics.ILInsts.
Require Import ChargeCore.Logics.BILInsts.
Require Import ChargeCore.Logics.ILogic.
Require Import ChargeCore.Logics.Later.

Require Import Java.Logic.AssertionLogic.
Require Import Java.Logic.SpecLogic.
Require Import Java.Language.Lang.
Require Import Java.Language.Program.

Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool.

Set Implicit Arguments.
Set Strict Implicit.

Inductive typ : Type :=
| tyArr : typ -> typ -> typ
| tyList : typ -> typ
| tyProd : typ -> typ -> typ
| tyBool : typ
| tyVal : typ
| tyString : typ
| tyNat : typ
| tyProp : typ
| tySpec : typ
| tyAsn : typ
| tyProg : typ
| tyMethod : typ
| tyCmd : typ
| tyDExpr : typ
| tySubst : typ.

Notation "'tyStack'" := (tyArr tyString tyVal).

Notation "'tyPure'" := (tyArr tyStack tyProp).
Notation "'tySasn'" := (tyArr tyStack tyAsn).
Notation "'tyExpr'" := (tyArr tyStack tyVal).
Notation "'tyFields'" := (tyList tyString).

Notation "'tyVarList'" := (tyList tyString).
Notation "'tyDExprList'" := (tyList tyDExpr).
Notation "'tySubstList'" := (tyList (tyProd tyString tyExpr)).

Fixpoint type_cast_typ (a b : typ) : option (a = b) :=
  match a as a , b as b return option (a = b) with
    | tyProp , tyProp => Some eq_refl
    | tySpec , tySpec => Some eq_refl
    | tyVal, tyVal => Some eq_refl
    | tyBool, tyBool => Some eq_refl
    | tyProg, tyProg => Some eq_refl
    | tyNat, tyNat => Some eq_refl
    | tyArr x y , tyArr a b =>
      match type_cast_typ x a , type_cast_typ y b with
        | Some pf , Some pf' =>
          Some (match pf in _ = t
                    , pf' in _ = t'
                      return tyArr x y = tyArr t t'
                with
                  | eq_refl , eq_refl => eq_refl
                end)
        | _ , _ => None
      end
    | tyProd x y , tyProd a b =>
      match type_cast_typ x a , type_cast_typ y b with
        | Some pf , Some pf' =>
          Some (match pf in _ = t
                    , pf' in _ = t'
                      return tyProd x y = tyProd t t'
                with
                  | eq_refl , eq_refl => eq_refl
                end)
        | _ , _ => None
      end
    | tyList x, tyList y =>
    	match type_cast_typ x y with
          | Some pf =>
    		Some (match pf in _ = t return tyList x = tyList t with
    			    | eq_refl => eq_refl
    			  end)
          | None => None
       end
    | tyString, tyString => Some eq_refl
    | tyCmd, tyCmd => Some eq_refl
    | tyMethod, tyMethod => Some eq_refl
    | tyDExpr, tyDExpr => Some eq_refl
    | tyAsn, tyAsn => Some eq_refl
    | tySubst, tySubst => Some eq_refl

    | _, _ => None
  end.

Lemma type_cast_typ_sound (a b : typ) :
	(exists pf, type_cast_typ a b = Some pf) <->
	a = b.
Proof.
  split; intros H.
  + destruct a, b; destruct H as [x _]; inversion x; subst; reflexivity.
  + subst. exists eq_refl. induction b; try reflexivity.
    simpl. rewrite IHb1, IHb2. reflexivity.
    simpl. rewrite IHb. reflexivity.
    simpl. rewrite IHb1, IHb2. reflexivity.
Qed.

Instance RelDec_eq_typ : RelDec (@eq typ) :=
{ rel_dec := fun a b => match type_cast_typ a b with
                          | None => false
                          | Some _ => true
                        end }.

Lemma type_cast_typ_refl (a : typ) : type_cast_typ a a = Some eq_refl.
Proof.
  induction a; simpl; try reflexivity.
  rewrite IHa1, IHa2; reflexivity.
  rewrite IHa. reflexivity.
  rewrite IHa1, IHa2; reflexivity.
Qed.

Instance RelDec_correct_typ : RelDec_Correct RelDec_eq_typ.
Proof.
	split; intros x y.
	destruct x, y; simpl; split; intro H; inversion H; subst; try reflexivity.
	+ remember (type_cast_typ x1 y1); destruct o; subst; [|inversion H].
	  remember (type_cast_typ x2 y2); destruct o; subst; [|inversion H].
	  reflexivity.
	+ do 2 rewrite type_cast_typ_refl; reflexivity.
	+ remember (type_cast_typ x y); destruct o; subst; [|inversion H].
	  reflexivity.
	+ rewrite type_cast_typ_refl. reflexivity.
	+ remember (type_cast_typ x1 y1); destruct o; subst; [|inversion H].
	  remember (type_cast_typ x2 y2); destruct o; subst; [|inversion H].
	  reflexivity.
	+ do 2 rewrite type_cast_typ_refl; reflexivity.
Qed.

Fixpoint typD (t : typ) : Type :=
  match t with
    | tyArr a b => typD a -> typD b
    | tyList a => @list (typD a)
    | tyProd a b => (typD a * typD b)%type
    | tyProp => Prop
    | tyNat => nat
    | tyBool => bool
    | tySpec => spec
    | tyAsn => asn
    | tyVal => val
    | tyString => string
    | tyProg => Program
    | tyMethod => Method
    | tyCmd => cmd
    | tyDExpr => dexpr
    | tySubst => @subst var val
  end.

Inductive tyAcc_typ : typ -> typ -> Prop :=
| tyAcc_tyArrL : forall a b, tyAcc_typ a (tyArr a b)
| tyAcc_tyArrR : forall a b, tyAcc_typ a (tyArr b a)
| tyAcc_tyProdL : forall a b, tyAcc_typ a (tyProd a b)
| tyAcc_tyProdR : forall a b, tyAcc_typ a (tyProd b a)
| tyAcc_tyList : forall a, tyAcc_typ a (tyList a).

Global Instance RType_typ : RType typ :=
{ typD := typD
; tyAcc := tyAcc_typ
; type_cast := type_cast_typ
}.

Global Instance Typ2_Fun : Typ2 _ Fun :=
{ typ2 := tyArr
; typ2_cast := fun _ _ => eq_refl
; typ2_match := fun T t tr =>
                  match t as t return T (typD t) -> T (typD t) with
                    | tyArr a b => fun _ => tr a b
                    | _ => fun fa => fa
                  end
}.

Global Instance Typ2Ok_Fun : Typ2Ok Typ2_Fun.
Proof.
  split; intros.
  + reflexivity.
  + apply (tyAcc_tyArrL).
  + apply (tyAcc_tyArrR).
  + unfold Rty in *. inversion H; subst; intuition congruence.
  + destruct x; try solve [right; reflexivity].
    left; exists x1, x2, eq_refl. reflexivity.
  + destruct pf; reflexivity.
Qed.

Global Instance Typ2_prod : Typ2 _ prod :=
{ typ2 := tyProd
; typ2_cast := fun _ _ => eq_refl
; typ2_match := fun T t tr =>
                  match t as t return T (typD t) -> T (typD t) with
                    | tyProd a b => fun _ => tr a b
                    | _ => fun fa => fa
                  end
}.

Global Instance Typ2Ok_prod : Typ2Ok Typ2_prod.
Proof.
  split; intros.
  + reflexivity.
  + apply (tyAcc_tyProdL).
  + apply tyAcc_tyProdR.
  + unfold Rty in *. inversion H; subst; intuition congruence.
  + destruct x; try solve [right; reflexivity].
    left; exists x1, x2, eq_refl. reflexivity.
  + destruct pf; reflexivity.
Qed.

Global Instance Typ1_list : Typ1 _ list :=
{ typ1 := tyList
; typ1_cast := fun _ => eq_refl
; typ1_match := fun T t tr =>
                  match t as t return T (typD t) -> T (typD t) with
                    | tyList a => fun _ => tr a
                    | _ => fun fa => fa
                  end
}.

Global Instance Typ1Ok_list : Typ1Ok Typ1_list.
Proof.
  split; intros.
  + reflexivity.
  + apply (tyAcc_tyList).
  + unfold Rty in *. inversion H; subst; intuition congruence.
  + destruct x; try solve [right; reflexivity].
    left; exists x, eq_refl. reflexivity.
  + destruct pf; reflexivity.
Qed.

Instance Typ0_Prop : Typ0 _ Prop :=
{ typ0 := tyProp
; typ0_cast := eq_refl
; typ0_match := fun T t tr =>
                  match t as t return T (typD t) -> T (typD t) with
                    | tyProp => fun _ => tr
                    | _ => fun fa => fa
                  end
}.

Instance Typ0Ok_Prop : Typ0Ok Typ0_Prop.
Proof.
    constructor.
    { reflexivity. }
    { destruct x; try solve [ right ; reflexivity ].
      { left. exists eq_refl. reflexivity. } }
    { destruct pf. reflexivity. }
Qed.

Instance Typ0_nat : Typ0 _ nat :=
{ typ0 := tyNat
; typ0_cast := eq_refl
; typ0_match := fun T t tr =>
                  match t as t return T (typD t) -> T (typD t) with
                    | tyNat => fun _ => tr
                    | _ => fun fa => fa
                  end
}.

Instance Typ0Ok_nat : Typ0Ok Typ0_nat.
Proof.
    constructor.
    { reflexivity. }
    { destruct x; try solve [ right ; reflexivity ].
      { left. exists eq_refl. reflexivity. } }
    { destruct pf. reflexivity. }
Qed.

Instance Typ0_bool : Typ0 _ bool :=
{ typ0 := tyBool
; typ0_cast := eq_refl
; typ0_match := fun T t tr =>
                  match t as t return T (typD t) -> T (typD t) with
                    | tyBool => fun _ => tr
                    | _ => fun fa => fa
                  end
}.

Instance Typ0Ok_bool : Typ0Ok Typ0_bool.
Proof.
    constructor.
    { reflexivity. }
    { destruct x; try solve [ right ; reflexivity ].
      { left. exists eq_refl. reflexivity. } }
    { destruct pf. reflexivity. }
Qed.

Instance Typ0_string : Typ0 _ string :=
{ typ0 := tyString
; typ0_cast := eq_refl
; typ0_match := fun T t tr =>
                  match t as t return T (typD t) -> T (typD t) with
                    | tyString => fun _ => tr
                    | _ => fun fa => fa
                  end
}.

Instance Typ0Ok_string : Typ0Ok Typ0_string.
Proof.
    constructor.
    { reflexivity. }
    { destruct x; try solve [ right ; reflexivity ].
      { left. exists eq_refl. reflexivity. } }
    { destruct pf. reflexivity. }
Qed.

Instance Typ0_val : Typ0 _ val :=
{ typ0 := tyVal
; typ0_cast := eq_refl
; typ0_match := fun T t tr =>
                  match t as t return T (typD t) -> T (typD t) with
                    | tyVal => fun _ => tr
                    | _ => fun fa => fa
                  end
}.

Instance Typ0Ok_val : Typ0Ok Typ0_val.
Proof.
    constructor.
    { reflexivity. }
    { destruct x; try solve [ right ; reflexivity ].
      { left. exists eq_refl. reflexivity. } }
    { destruct pf. reflexivity. }
Qed.

Instance RTypeOk_typ : @RTypeOk _ RType_typ.
Proof.
  split; intros.
  + reflexivity.
  + unfold well_founded.
    intros. induction a; simpl; constructor; intros; inversion H; subst; assumption.
  + destruct pf; reflexivity.
  + destruct pf1, pf2; reflexivity.
  + apply type_cast_typ_refl.
  + intro H1. inversion H1; subst.
    rewrite type_cast_typ_refl in H. inversion H.
  + intros x.
    induction x; intros y; destruct y; try (right; congruence); try (left; congruence).
    * destruct (IHx1 y1) as [Hx1 | Hx1]; clear IHx1;
      destruct (IHx2 y2) as [Hx2 | Hx2]; clear IHx2;
      try (right; congruence); try (left; congruence).
    * destruct (IHx y) as [Hx | Hx]; clear IHx; [
	left; congruence | right; congruence].
    * destruct (IHx1 y1) as [Hx1 | Hx1]; clear IHx1;
      destruct (IHx2 y2) as [Hx2 | Hx2]; clear IHx2;
      try (right; congruence); try (left; congruence).
Qed.


Definition null' : TypesI.typD tyVal := null.
(*
Program Instance SubstTypeD_typ : @SubstTypeD typ _ _ _ := {
	stSubst := eq_refl
}.
*)
Definition should_not_be_necessary : ILogicOps (TypesI.typD tySpec).
Proof.
  simpl.
  apply _.
Defined.

Definition should_also_not_be_necessary : ILLOperators (TypesI.typD tySpec).
Proof.
  simpl.
  apply _.
Defined.

  Definition ilops : @logic_ops _ RType_typ :=
  fun t =>
    match t
          return option (ILogic.ILogicOps (TypesI.typD t))
    with
      | tyProp => Some _
      | tyAsn => Some _
      | tySasn => Some (@ILFun_Ops stack asn _)
      | tySpec => Some should_not_be_necessary
      | tyPure => Some ( @ILFun_Ops stack Prop _)
      | _ => None
    end.

  Definition bilops : @bilogic_ops _ RType_typ :=
  fun t =>
    match t
          return option (BILogic.BILOperators (TypesI.typD t))
    with
      | tyAsn => Some _
      | tySasn => Some (@BILFun_Ops stack asn _)
      | _ => None
    end.

Definition eops : @embed_ops _ RType_typ :=
  fun t u =>
    match t as t , u as u
          return option
                   (ILEmbed.EmbedOp (TypesI.typD t) (TypesI.typD u))
    with
      | tyPure, tySasn => Some _
      | tyProp, tyAsn => Some _
      | _ , _ => None
    end.
(*
Definition lops : @later_ops _ RType_typ :=
  fun t =>
    match t return option (ILLOperators (TypesI.typD t)) with
	  | tySpec => Some should_also_not_be_necessary
	  | _ => None
    end.
*)
Definition ilp : il_pointwise :=
  fun t =>
    match t with
      | tySasn => true
      | tyPure => true
      | _ => false
    end.

Definition bilp : bil_pointwise :=
  fun t =>
    match t with
      | tySasn => true
      | _ => false
    end.

Definition eilp : eil_pointwise :=
  fun t u =>
    match t, u with
      | tyStack, tyProp => true
      | tyStack, tyAsn => true
      | _, _ => false
    end.
(*
Lemma eilpOk : eil_pointwiseOk eops eilp.
Proof.
  intros t u; simpl.
  destruct t; try apply I.
  destruct u; try apply I.
  remember (type_cast_typ t1 u1).
  destruct o; try apply I.
  destruct t1; subst.
  destruct t1_1.
  Focus 6.
  destruct t1_2.
  Focus 5.
  destruct t2.
  Focus 8.
  destruct u2.
  Focus 10.
  match goal with
    |- match ?a with | Some _ => _ | None => _ end => remember a
  end.
  destruct o.
  intros.
  pose proof eilf_pointwise_embed_eq (gs := eops) (eilp := eilp).
  rewrite @eilf_pointwise_embed_eq.
  simpl. reflexivity.
  Print il_pointwiseOk.
  simpl.
  unfold Denotation.tyArrD, Denotation.tyArrD', Denotation.trmD, Denotation.tyArrR, Denotation.tyArrR', Denotation.trmR, eq_rect_r, eq_rect, eq_sym, id.
  simpl.
  unfold ILEmbed.embed.
  simpl.
  destruct e.
  simpl. reflexivity.
  reflexivity.
  remember (eops tyProp tySasn).
  destruct o.
  rewrite <- Heqo0.
Print eil_pointwiseOk.
*)
(*
Lemma ilpOk : il_pointwiseOk ilops ilp.
Proof.
  intros t; simpl; destruct t; try apply I.
  destruct t1; simpl; try apply I.
  destruct t1_1; try apply I.
  destruct t1_2; try apply I.
  destruct t2; simpl; try apply I.
  repeat split.
  repeat split.
Qed.

Lemma BilpOk : bil_pointwiseOk bilops bilp.
Proof.
  intros t; simpl; destruct t; try apply I.
  destruct t1; simpl; try apply I.
  destruct t1_1; try apply I.
  destruct t1_2; try apply I.
  destruct t2; simpl; try apply I.
  repeat split.
Qed.
*)
Fixpoint edt (t : typ) : typD t -> typD t -> option bool :=
  match t return typD t -> typD t -> option bool with
    | tyBool => fun e1 e2 => Some (e1 ?[ eq ] e2)
    | tyVal => fun e1 e2 => Some (e1 ?[ eq ] e2)
    | tyString => fun e1 e2 => Some (e1 ?[ eq ] e2)
    | tyNat => fun e1 e2 => Some (e1 ?[ eq ] e2)
    | tyProg => fun e1 e2 => Some (e1 ?[ eq ] e2)
    | tyCmd => fun e1 e2 => Some (e1 ?[ eq ] e2)
    | tyDExpr => fun e1 e2 => Some (e1 ?[ eq ] e2)
    | tyList tyString => fun e1 e2 => Some (e1 ?[ eq ] e2)
    | tyProd t1 t2 =>
      fun e1 e2 =>
        match edt t1 (fst e1) (fst e2), edt t2 (snd e1) (snd e2) with
          | Some a, Some b => Some (a && b)
          | _, _ => None
        end
    | _ => fun _ _ => None
  end.
(*
Instance SemiEqDecTyp_edt : SemiEqDecTyp typ := {
    semi_eq_dec_typ := edt
  }.

Definition edtOk : 
  forall t a b,
    match edt t a b with
      | Some true => a = b
      | Some false => a <> b
      | None => True
    end.
Proof.
  induction t; simpl in *; intros; try apply I; try (consider (e1 ?[ eq ] e2); intuition congruence).
  destruct t; simpl in *; try apply I.
  consider (a ?[ eq ] b); intuition congruence.
  destruct a, b; simpl.
  forward. inv_all; subst. 
  specialize (IHt1 t t3); specialize (IHt2 t0 t4).
  destruct b0, b1; rewrite H in IHt1; rewrite H0 in IHt2; simpl; intuition congruence.
  consider (a ?[ eq ] b); intuition congruence.
  consider (a ?[ eq ] b); intuition congruence.
  consider (a ?[ eq ] b); intuition congruence.
  consider (a ?[ eq ] b); intuition congruence.
  consider (a ?[ eq ] b); intuition congruence.
  consider (a ?[ eq ] b); intuition congruence.
  consider (a ?[ eq ] b); intuition congruence.
Qed.

Instance SemiEqDecTypOk_edt : SemiEqDecTypOk SemiEqDecTyp_edt := {
    semi_eq_dec_typOk := edtOk
  }.

*)