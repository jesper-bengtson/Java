Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Data.POption.
Require Import ExtLib.Tactics.

Require Import MirrorCore.TypesI.
Require Import MirrorCore.MTypes.ModularTypes.
Require Import MirrorCore.MTypes.ListType.
Require Import MirrorCore.MTypes.ProdType.
Require Import MirrorCore.MTypes.BaseType.
Require Import MirrorCore.syms.SymOneOf.
Require Import MirrorCore.Views.FuncView.
Require Import MirrorCore.Views.ViewSumN.
Require Import MirrorCore.MTypes.ListType.

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
Require Import Java.Func.JavaType.

Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool.

Set Implicit Arguments.
Set Strict Implicit.

Import OneOfType.

Definition typ_map x := 
  list_to_pmap 
    (prod_typ x :: 
     list_typ x :: 
     base_typ x :: 
     java_typ x :: 
     nil).

Definition typ' x := OneOfType.OneOf (typ_map x).
Definition typ := mtyp typ'.

Ltac pmap_lookup'_simpl :=
  repeat (
    match goal with 
    | H : match pmap_lookup' Empty ?p with | _Some _ => _ | _None => Empty_set end |- _ => 
      exfalso; clear -H; rewrite pmap_lookup'_Empty in H; destruct H
    | H : match pmap_lookup' _ ?p with | _Some _ => _ | _None => Empty_set end |- _ => 
      destruct p; simpl in H
    end).

Ltac eq_dec_right :=
  let H := fresh "H" in
    right; intro H; inv_all; congruence.

Definition typ'_dec {n} (a : typ' n) : forall b, {a = b} + {a <> b}.
Proof.
  intros.
  destruct a as [a1 v1].
  destruct b as [a2 v2].
  unfold typ_map, list_to_pmap in *. simpl in *.
  pmap_lookup'_simpl; try eq_dec_right.  
  pose proof (base_typ_dec v1 v2).
  destruct H; [left; subst; reflexivity|].
  right; intros H; apply n0; inv_all; subst.
  assert (x = eq_refl) by (apply UIP_refl); subst. reflexivity.
  pose proof (java_typ_dec v1 v2).
  destruct H; [left; subst; reflexivity|].
  right; intros H; apply n0; inv_all; subst.
  assert (x = eq_refl) by (apply UIP_refl); subst. reflexivity.
  pose proof (list_typ_dec v1 v2).
  destruct H; [left; subst; reflexivity|].
  right; intros H; apply n0; inv_all; subst.
  assert (x = eq_refl) by (apply UIP_refl); subst. reflexivity.
  pose proof (prod_typ_dec v1 v2).
  destruct H; [left; subst; reflexivity|].
  right; intros H; apply n0; inv_all; subst.
  assert (x = eq_refl) by (apply UIP_refl); subst. reflexivity.
Defined.

Definition typ'D {n} (t : typ' n) : type_for_arity n.
unfold typ', typ_map, list_to_pmap in t; simpl in t.
destruct t as [p v].
pmap_lookup'_simpl.
apply base_typD; assumption.
apply java_typD; assumption.
apply list_typD; assumption.
apply prod_typD; assumption.
Defined.


Global Instance TypeView_prod_typ' : FuncView (typ' 2) (prod_typ 2) :=
  FuncViewPMap 1 (typ_map 2) eq_refl.
  
Global Instance TypeView_list_typ' : FuncView (typ' 1) (list_typ 1) :=
  FuncViewPMap 2 (typ_map 1) eq_refl.
  
Global Instance TypeView_base_typ' : FuncView (typ' 0) (base_typ 0) :=
  FuncViewPMap 3 (typ_map 0) eq_refl.
  
Global Instance TypeView_java_typ' : FuncView (typ' 0) (java_typ 0) :=
  FuncViewPMap 4 (typ_map 0) eq_refl.
  
Instance TypeView_prod_typ : FuncView typ (prod_typ 2 * typ * typ).
eapply FuncView_trans. 
apply FuncView_sym2.
eapply (@FuncView_prod _ _ _ _ (@FuncView_prod _ _ _ _ _ FuncView_id) FuncView_id). 
Defined.

Instance TypeView_list_typ : FuncView typ (list_typ 1 * typ).
eapply FuncView_trans. 
apply FuncView_sym1.
eapply (@FuncView_prod _ _ _ _ _ FuncView_id). 
Defined.

Instance TypeView_base_typ : FuncView typ (base_typ 0).
eapply FuncView_trans. 
eapply FuncView_sym0.
apply TypeView_base_typ'.
Defined.

Instance TypeView_java_typ : FuncView typ (java_typ 0).
eapply FuncView_trans. 
eapply FuncView_sym0.
apply TypeView_java_typ'.
Defined.

Notation "'tyStack'" := (tyArr tyString tyVal).

Notation "'tyPure'" := (tyArr tyStack tyProp).
Notation "'tySasn'" := (tyArr tyStack tyAsn).
Notation "'tyExpr'" := (tyArr tyStack tyVal).
Notation "'tyFields'" := (tyList tyString).

Notation "'tyVarList'" := (tyList tyString).
Notation "'tyDExprList'" := (tyList tyExpr).
Notation "'tySubstList'" := (tyList (tyProd tyString tyExpr)).

Instance TSym_typ' : TSym typ' := { 
  symbolD := @typ'D; 
  symbol_dec := @typ'_dec 
}.


(* Instantiate the RType interface *)
Instance RType_typ : RType typ := RType_mtyp typ' _.
Instance RTypeOk_typ : RTypeOk := @RTypeOk_mtyp typ' _.

(* Build instances for describing functions and Prop *)
Instance Typ2_tyArr : Typ2 RType_typ Fun := Typ2_Fun.
Instance Typ2Ok_tyArr : Typ2Ok Typ2_tyArr := Typ2Ok_Fun.

Instance Typ0_tyProp : Typ0 RType_typ Prop := Typ0_sym tyProp.
Instance Typ0Ok_tyProp : Typ0Ok Typ0_tyProp := Typ0Ok_sym tyProp.

Instance Typ0_tyNat : Typ0 RType_typ nat := Typ0_sym tyNat.
Instance Typ0Ok_tyNat : Typ0Ok Typ0_tyNat := Typ0Ok_sym tyNat.

Instance Typ0_tyString : Typ0 RType_typ string := Typ0_sym tyString.
Instance Typ0Ok_tyString : Typ0Ok Typ0_tyString := Typ0Ok_sym tyString.

Instance Typ0_tyBool : Typ0 RType_typ bool := Typ0_sym tyBool.
Instance Typ0Ok_tyBool : Typ0Ok Typ0_tyBool := Typ0Ok_sym tyBool.

Instance Typ1_tyList : Typ1 RType_typ list := Typ1_sym (f_insert tList).
Instance Typ1Ok_tyList : Typ1Ok Typ1_tyList := Typ1Ok_sym (f_insert tList).

Instance Typ2_tyProd : Typ2 RType_typ prod := Typ2_sym (f_insert tProd).
Instance Typ2Ok_tyProd : Typ2Ok Typ2_tyProd := Typ2Ok_sym (f_insert tProd).




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
Print typ.
Print mtyp.
Print tyProp.
Print base_typ.
Check @f_view.
Print logic_ops.
Print RType_typ.
Print typ.
Print typ'.
Print typ'.
Check @f_view typ (base_typ 0) _ tyProp.
Check typ0_match.
  Definition ilops : @logic_ops typ RType_typ.
                       refine (
  fun t =>
    match @f_view typ (base_typ 0) TypeView_base_typ t as x 
          return x = @f_view typ (base_typ 0) TypeView_base_typ t -> poption (ILogic.ILogicOps (TypesI.typD t)) with
      | pSome p =>
        match p in base_typ 0 with
        | tProp => fun pf => pSome _
        | _ => fun _ => pNone
        end
      | _ => fun _ => pNone
    end eq_refl).

(*      | tyAsn => pSome _
      | tySasn => _Some (@ILFun_Ops stack asn _)
      | tySpec => _Some should_not_be_necessary
      | tyPure => _Some (@ILFun_Ops stack Prop _)*)
      | _ => fun _ => pNone
    end eq_refl).
  destruct t; try congruence.
SearchAbout asNth.
unfold typ' in t.
simpl in *.
assert ({x :
    match pmap_lookup' (typ_map 0) 3 return TypeR with
    | _Some T => T
    | _None => Empty_set
    end & asNth 3 t = Some x}) by (destruct (asNth 3 t); [eexists; reflexivity|congruence]).
destruct X.
rewrite e in H0.
simpl in *.
inversion H0; subst.
pose proof (asNth_eq 3 t e).
subst. simpl.
apply (@pSome (ILogicOps Prop)).
apply _.
Defined.


  Print asNth'.
  unfold asNth, asNth' in *. simpl in *.
  destruct t; simpl in *.
  destruct index0; simpl in *; try congruence.
  destruct index0; simpl in *; try congruence.
  inversion H0; subst. simpl.
  inv_all; subst.
  apply pSome. apply _.
Defined.
  assert (index0 = (3%positive)). admit.
  subst. simpl in *.
  revert H0.
  remember (pmap_lookup' (typ_map 0) index0).
  simpl in *.
remember (asNth 3 t) as o.
destruct o; try congruence.
simpl. apply pSome. inversion H0. subst.
destruct t. simpl in *.
SearchAbout asNth.
subst.
simpl in *.
unfold asNth, asNth' in Heqo. simpl in *.
inv_all. subst. simpl. apply _.
unfold typ'D.
simpl.
rewrite <- Heqo.
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

*) *)