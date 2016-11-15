Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Data.PList.
Require Import ExtLib.Data.POption.
Require Import ExtLib.Tactics.
Require Import ExtLib.Data.Eq.UIP_trans.

Require Import MirrorCore.TypesI.
Require Import MirrorCore.CTypes.CoreTypes.
Require Import MirrorCore.CTypes.ListType.
Require Import MirrorCore.CTypes.ProdType.
Require Import MirrorCore.CTypes.BaseType.
Require Import MirrorCore.CTypes.TSymOneOf.
Require Import MirrorCore.Views.FuncView.
Require Import MirrorCore.Views.View.
Require Import MirrorCore.Views.ViewSumN.

Require Import Charge.Views.ILogicView.
Require Import Charge.Views.BILogicView.
Require Import Charge.Views.EmbedView.
Require Import ChargeCore.Open.Subst.
Require Import ChargeCore.Logics.ILInsts.
Require Import ChargeCore.Logics.BILInsts.
Require Import ChargeCore.Logics.ILogic.
Require Import ChargeCore.Logics.BILogic.
Require Import ChargeCore.Logics.ILEmbed.

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

Definition typ_map :=
  list_to_pmap
    (pcons prod_typ (pcons list_typ (pcons base_typ (pcons java_typ pnil)))).

Lemma pmap_lookup'_Empty p : pmap_lookup' Empty p = _None.
Proof.
  induction p; simpl in *; try apply IHp. reflexivity.
Qed.

Definition typ' := OneOfType.OneOfF typ_map.

Definition TSymAll_typ_map : TSym_All typ_map.
  repeat first [eapply TSym_All_Branch_None |
                eapply TSym_All_Branch_Some; [eapply _ | |] |
                eapply TSym_All_Empty].
Defined.

Global Instance TSym_typ' : TSym typ'.
  apply TSymOneOf. apply TSymAll_typ_map.
Defined.

Definition typ : Set := ctyp typ'.

Global Instance RType_typ : RType typ.
apply RType_ctyp. apply _.
Defined.

Global Instance RTypeOk_typ : RTypeOk.
apply RTypeOk_ctyp.
Defined.

Global Instance TypeView_prod_typ' : PartialView (typ' 2) (prod_typ 2) :=
  PartialViewPMap_Type 1 typ_map eq_refl 2.

Global Instance TypeView_list_typ' : PartialView (typ' 1) (list_typ 1) :=
  PartialViewPMap_Type 2 typ_map eq_refl 1.

Global Instance TypeView_base_typ' : PartialView (typ' 0) (base_typ 0) :=
  PartialViewPMap_Type 3 typ_map eq_refl 0.

Global Instance TypeView_java_typ' : PartialView (typ' 0) (java_typ 0) :=
  PartialViewPMap_Type 4 typ_map eq_refl 0.

Global Instance TypeView_prod_typ : PartialView typ (prod_typ 2 * (typ * typ)).
eapply PartialView_trans.
apply TypeView_sym2.
eapply (@PartialView_prod _ _ _ _ _ PartialView_id).
Defined.

Global Instance TypeView_list_typ : PartialView typ (list_typ 1 * typ).
eapply PartialView_trans.
apply TypeView_sym1.
eapply (@PartialView_prod _ _ _ _ _ PartialView_id).
Defined.

Global Instance TypeView_base_typ : PartialView typ (base_typ 0).
eapply PartialView_trans.
eapply TypeView_sym0.
apply TypeView_base_typ'.
Defined.

Global Instance TypeView_java_typ : PartialView typ (java_typ 0).
eapply PartialView_trans.
eapply TypeView_sym0.
apply TypeView_java_typ'.
Defined.

Require Import MirrorCore.Views.TypeView.

Arguments PartialViewOk_prod {_ _ _ _ _ _ _ _} _ _ : clear implicits.

Definition TypeViewOk_prod_typ
: TypeViewOk typD (fun x => (prod_typD (n:=2) (fst x)) (typD (fst (snd x))) (typD (snd (snd x))))
             TypeView_prod_typ.
Proof.
  eapply PartialView_transOk.
  eapply TypeViewOk_sym2.
  eapply PartialViewOk_prod.
  eapply PartialViewOk_TSymOneOf with (p := 1%positive) (H := TSymAll_typ_map).
  eapply PartialViewOk_id; eapply eq_Reflexive.
  unfold type_equiv. inversion 2.
  etransitivity.
  eapply H.
  simpl in *. simpl in *. rewrite H1. rewrite H2. reflexivity.
Defined.

Definition TypeViewOk_list_typ
: TypeViewOk typD (fun x => (list_typD (n:=1) (fst x)) (typD (snd x)))
             TypeView_list_typ.
Proof.
  eapply PartialView_transOk.
  eapply TypeViewOk_sym1.
  eapply PartialViewOk_prod.
  eapply PartialViewOk_TSymOneOf with (p := 2%positive) (H := TSymAll_typ_map).
  eapply PartialViewOk_id; eapply eq_Reflexive.
  unfold type_equiv. inversion 2.
  etransitivity.
  eapply H.
  simpl in *. simpl in *. rewrite H1. rewrite H2. reflexivity.
Defined.

Definition TypeViewOk_base_typ : TypeViewOk typD (@base_typD 0) TypeView_base_typ.
eapply PartialView_transOk.
eapply TypeViewOk_sym0.
eapply PartialViewOk_TSymOneOf with (p := 3%positive) (H := TSymAll_typ_map).
simpl; intros. unfold type_equiv in *.
etransitivity; [apply H|apply H0].
Defined.

Definition TypeViewOk_java_typ : TypeViewOk typD (@java_typD 0) TypeView_java_typ.
eapply PartialView_transOk.
eapply TypeViewOk_sym0.
eapply PartialViewOk_TSymOneOf with (p := 4%positive) (H := TSymAll_typ_map).
simpl; intros. unfold type_equiv in *.
etransitivity; [apply H|apply H0].
Defined.

Arguments tyArr {_} _ _.

Notation "'tyStack'" := (tyArr tyString tyVal).

Notation "'tyPure'" := (tyArr tyStack tyProp).
Notation "'tySasn'" := (tyArr tyStack tyAsn).
Notation "'tyExpr'" := (tyArr tyStack tyVal).
Notation "'tyFields'" := (tyList tyString).

Notation "'tyStringList'" := (tyList tyString).
Notation "'tyDExprList'" := (tyList tyExpr).
Notation "'tySubstList'" := (tyList (tyProd tyString tyExpr)).

(* Build instances for describing functions and Prop *)
Global Instance Typ2_tyArr : Typ2 RType_typ Fun := Typ2_Fun.
Global Instance Typ2Ok_tyArr : Typ2Ok Typ2_tyArr := Typ2Ok_Fun.

Global Instance Typ0_tyProp : Typ0 RType_typ Prop := Typ0_sym tyProp.
Global Instance Typ0Ok_tyProp : Typ0Ok Typ0_tyProp := Typ0Ok_sym tyProp.

Global Instance Typ0_tyNat : Typ0 RType_typ nat := Typ0_sym tyNat.
Global Instance Typ0Ok_tyNat : Typ0Ok Typ0_tyNat := Typ0Ok_sym tyNat.

Global Instance Typ0_tyString : Typ0 RType_typ string := Typ0_sym tyString.
Global Instance Typ0Ok_tyString : Typ0Ok Typ0_tyString := Typ0Ok_sym tyString.

Global Instance Typ0_tyVal : Typ0 RType_typ val := Typ0_sym (ts:=TSym_typ') (@tyVal _ _).
Global Instance Typ0Ok_tyVal : Typ0Ok Typ0_tyVal := Typ0Ok_sym tyVal.

Global Instance Typ0_tyBool : Typ0 RType_typ bool := Typ0_sym tyBool.
Global Instance Typ0Ok_tyBool : Typ0Ok Typ0_tyBool := Typ0Ok_sym tyBool.

Global Instance Typ1_tyList : Typ1 RType_typ list := Typ1_sym (f_insert tList).
Global Instance Typ1Ok_tyList : Typ1Ok Typ1_tyList := Typ1Ok_sym (f_insert tList).

Global Instance Typ2_tyProd : Typ2 RType_typ prod := Typ2_sym (f_insert tProd).
Global Instance Typ2Ok_tyProd : Typ2Ok Typ2_tyProd := Typ2Ok_sym (f_insert tProd).

Definition null' : TypesI.typD tyVal := null.

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

Definition pv_elim {T U : Type} {Pv : PartialView T U} {Z} {PVo : PartialViewOk Pv Z} (F : T -> Type) (x : T)
: (forall y, F (f_insert y)) ->
  (unit -> F x) ->
  F x :=
  match f_view x as Z return f_view x = Z -> _
  with
  | pSome v => fun pf X _ => 
                 match (match pv_ok _ _ with | conj A _ => A end) pf in _ = Z return F Z with
                 | eq_refl => X v
                 end
  | pNone => fun _ _ X => X tt
  end eq_refl.

Arguments pv_elim {_ _ _ _ _} _ _ {_} _.

Existing Instance should_not_be_necessary.

Definition prop_match := prop_match (FVOk := TypeViewOk_base_typ).
Definition asn_match := asn_match (FVOk := TypeViewOk_java_typ).
Definition spec_match := spec_match (FVOk := TypeViewOk_java_typ).
Definition string_match := string_match (FVOk := TypeViewOk_base_typ).
Definition val_match := val_match (FVOk := TypeViewOk_java_typ).

Definition ilops : @logic_ops typ RType_typ :=
  fun t =>
    prop_match 
      (fun x => poption (ILogicOps (typD x))) t
      (pSome _)
      (fun _ => 
         asn_match 
           (fun x => poption (ILogicOps (typD x))) t 
           (pSome _)
           (fun _ => 
              spec_match 
                (fun x => poption (ILogicOps (typD x))) t 
                (pSome _)
                (fun _ => 
                   match t with
                   | tyArr (tyArr t1 t2) t3 => 
                     (string_match 
                        (fun x => poption (ILogicOps ((typD x -> typD t2) -> typD t3))) t1
                        (val_match
                           (fun x => poption (ILogicOps ((string -> typD x) -> typD t3))) t2
                           (prop_match 
                              (fun x => poption (ILogicOps (stack -> typD x))) t3
                              (pSome _)
                              (fun _ => 
                                 asn_match 
                                   (fun x => poption (ILogicOps (stack -> typD x))) t3 
                                   (pSome _)
                                   (fun _ => pNone)))
                           (fun _ => pNone))
                        (fun _ => pNone))
                   | _ => pNone
                   end))).

Definition bilops : @bilogic_ops typ RType_typ :=
  fun t =>
    asn_match 
      (fun x => poption (BILOperators (typD x))) t 
      (pSome _)
      (fun _ => 
         match t with
         | tyArr (tyArr t1 t2) t3 =>
           (string_match 
              (fun x => poption (BILOperators ((typD x -> typD t2) -> typD t3))) t1
              (val_match
                 (fun x => poption (BILOperators ((string -> typD x) -> typD t3))) t2
                 (asn_match 
                    (fun x => poption (BILOperators (stack -> typD x))) t3 
                    (pSome _)
                    (fun _ => pNone))
                 (fun _ => pNone))
              (fun _ => pNone))
         | _ => pNone
         end).

Definition eops : @embed_ops typ RType_typ :=
  fun t u =>
    prop_match 
      (fun x => option (EmbedOp (typD x) (typD u))) t 
      (asn_match 
         (fun x => option (EmbedOp Prop (typD x))) u
         (Some _)
         (fun _ => None))
      (fun _ => 
         match t, u with
         | tyArr (tyArr t1 t2) t3, tyArr (tyArr u1 u2) u3 =>
           (string_match 
              (fun x => option (EmbedOp ((typD x -> typD t2) -> typD t3) 
                                        ((typD u1 -> typD u2) -> typD u3))) t1
              (val_match
                 (fun x => option (EmbedOp ((string -> typD x) -> typD t3) 
                                           ((typD u1 -> typD u2) -> typD u3))) t2
                 (prop_match 
                    (fun x => option (EmbedOp (stack -> typD x)
                                              ((typD u1 -> typD u2) -> typD u3))) t3
                    (string_match 
                       (fun x => option (EmbedOp (stack -> Prop)
                                                 ((typD x -> typD u2) -> typD u3))) u1
                       (val_match
                          (fun x => option (EmbedOp (stack -> Prop)
                                                    ((string -> typD x) -> typD u3))) u2
                          (asn_match 
                             (fun x => option (EmbedOp (stack -> Prop)
                                                       (stack -> typD x))) u3
                             (Some _)
                             (fun _ => None))
                          (fun _ => None))
                       (fun _ => None))
                    (fun _ => None))
                 (fun _ => None))
              (fun _ => None))
         | _, _ => None
         end).