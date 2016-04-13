Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Data.PList.
Require Import ExtLib.Data.POption.
Require Import ExtLib.Tactics.
Require Import ExtLib.Data.Eq.UIP_trans.

Require Import MirrorCore.TypesI.
Require Import MirrorCore.MTypes.ModularTypes.
Require Import MirrorCore.MTypes.ListType.
Require Import MirrorCore.MTypes.ProdType.
Require Import MirrorCore.MTypes.BaseType.
Require Import MirrorCore.MTypes.TSymOneOf.
Require Import MirrorCore.Views.FuncView.
Require Import MirrorCore.Views.View.
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

Definition typ_map := 
  list_to_pmap
    (pcons prod_typ (pcons list_typ (pcons base_typ (pcons java_typ pnil)))).

Lemma pmap_lookup'_Empty p : pmap_lookup' Empty p = _None.
Proof.
  induction p; simpl in *; try apply IHp. reflexivity.
Qed.
(*
Definition OneOf_Branch_left n l r (H : OneOfF l) : OneOf (Branch n l r).
Proof.
  destruct H.
  exists (xO index0); simpl; apply value0.
Defined.

Definition OneOf_Branch_right n l r (H : OneOf r) : OneOf (Branch n l r).
Proof.
  destruct H.
  exists (xI index0); simpl; apply value0.
Defined.

Definition OneOf_Branch_node n l r (H : n) : OneOf (Branch (_Some n) l r).
Proof.
  exists xH; simpl; apply H.
Defined.


Definition OneOf_Branch n l r (H : OneOf (Branch (_Some n) l r)) :   
  n + OneOf l + OneOf r.
Proof.
  remember (Branch (_Some n) l r).
  generalize dependent l; generalize dependent r.
  induction p; intros; inversion Heqp; subst.
  destruct H. destruct index0; [right | left; right | left; left; assumption]; simpl in *.
  exists index0; assumption.
  exists index0; assumption.
Defined.
*)
Definition typ' := OneOfType.OneOfF typ_map. 
(*
Instance TSym_Empty : TSym 
Proof.
  split; intros.
  apply OneOf_Empty in X; destruct X.
  exfalso. apply OneOf_Empty in a; destruct a.
Defined.

Instance TSym_Branch n l r 
         (Hl : TSym (fun x => OneOf (l x)))
         (Hr : TSym (fun x => OneOf (r x)))
         (Hn : TSym n) :
  TSym (fun x => (OneOf (Branch (_Some (n x)) (l x) (r x)))).
Proof.
  split; intros.
  apply OneOf_Branch in X. destruct X as [[X | X] | X].
  eapply @symbolD in Hn; eassumption.
  eapply @symbolD in Hl; eassumption.
  eapply @symbolD in Hr; eassumption.
  destruct a, b; simpl.

  destruct index0, index1; try (solve [right; intros H; inv_all; subst; inversion x]).
  + eapply @symbol_dec with (a := mkOneOf _ index0 value0) (b := mkOneOf _ index1 value1) in Hr.
    destruct Hr; [left | right]; inv_all; subst; [reflexivity|].
    intros H. apply n1. inv_all. inversion x; subst. 
    rewrite (uip_trans Pos.eq_dec _ _ x eq_refl) in *. reflexivity.
  + eapply @symbol_dec with (a := mkOneOf _ index0 value0) (b := mkOneOf _ index1 value1) in Hl.
    destruct Hl; [left | right]; inv_all; subst; [reflexivity|].
    intros H. apply n1. inv_all. inversion x; subst. 
    rewrite (uip_trans Pos.eq_dec _ _ x eq_refl) in *. reflexivity.
  + eapply @symbol_dec with (a := value0) (b := value1) in Hn.
    destruct Hn; [left | right]; subst; [reflexivity|].
    intros H. apply n1. inv_all. inversion x; subst. 
    rewrite (uip_trans Pos.eq_dec _ _ x eq_refl) in *. reflexivity.
Defined.
*)
Definition TSymAll_typ_map : TSym_All typ_map.
  repeat first [eapply TSym_All_Branch_None | 
                eapply TSym_All_Branch_Some; [eapply _ | |] | 
                eapply TSym_All_Empty]. 
Defined.

Global Instance TSym_typ' : TSym typ'.
  apply TSymOneOf. apply TSymAll_typ_map.
Defined.

Definition typ := mtyp typ'.

Global Instance RType_typ : RType typ. 
apply RType_mtyp. apply _.
Defined.

Global Instance RTypeOk_typ : RTypeOk. 
apply RTypeOk_mtyp. 
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

Definition TypeViewOk_prod_typ
: TypeViewOk typD (fun x => (prod_typD (n:=2) (fst x)) (typD (fst (snd x))) (typD (snd (snd x))))
             TypeView_prod_typ.
Proof.
  eapply PartialView_transOk.
  eapply TypeViewOk_sym2.
  About PartialView_prodOk.
  Arguments PartialView_prodOk {_ _ _ _ _ _ _ _} _ _ : clear implicits.
  eapply PartialView_prodOk.
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
  About PartialView_prodOk.
  Arguments PartialView_prodOk {_ _ _ _ _ _ _ _} _ _ : clear implicits.
  eapply PartialView_prodOk.
  eapply PartialViewOk_TSymOneOf with (p := 2%positive) (H := TSymAll_typ_map).
  About PartialViewOk_id.
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

Global Instance Typ0_tyBool : Typ0 RType_typ bool := Typ0_sym tyBool.
Global Instance Typ0Ok_tyBool : Typ0Ok Typ0_tyBool := Typ0Ok_sym tyBool.

Global Instance Typ1_tyList : Typ1 RType_typ list := Typ1_sym (f_insert tList).
Global Instance Typ1Ok_tyList : Typ1Ok Typ1_tyList := Typ1Ok_sym (f_insert tList).

Global Instance Typ2_tyProd : Typ2 RType_typ prod := Typ2_sym (f_insert tProd).
Global Instance Typ2Ok_tyProd : Typ2Ok Typ2_tyProd := Typ2Ok_sym (f_insert tProd).




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

Definition ilops : @logic_ops typ RType_typ.
  refine (
      fun t =>
        match @f_view typ (base_typ 0) TypeView_base_typ t as x 
              return x = @f_view typ (base_typ 0) TypeView_base_typ t -> poption (ILogic.ILogicOps (TypesI.typD t)) with
        | pSome p =>
          fun pf =>
            match p as x in base_typ 0 return p = x -> poption (ILogic.ILogicOps (TypesI.typD t)) with
            | tProp => fun pf' => pSome _
            | _ => fun _ => pNone
            end eq_refl
        | _ => 
          fun _ =>
            match @f_view typ (java_typ 0) TypeView_java_typ t as x 
                  return x = @f_view typ (java_typ 0) TypeView_java_typ t -> poption (ILogic.ILogicOps (TypesI.typD t)) with
            | pSome p =>
              fun pf =>
                match p as x in java_typ 0 return p = x -> poption (ILogic.ILogicOps (TypesI.typD t)) with
                | tAsn => fun pfAsn => pSome _
                | tSpec => fun pfSpec => pSome _
                | _ => fun _ => pNone
                end eq_refl
            | pNone => 
              fun _ => 
                match t as x return t = x -> poption (ILogic.ILogicOps (TypesI.typD t)) with
                | tyArr (tyArr t1 t2) t3 => 
                  fun _ =>
                  match @f_view typ (base_typ 0) TypeView_base_typ t1 as x 
                        return x = @f_view typ (base_typ 0) TypeView_base_typ t1 -> poption (ILogic.ILogicOps (TypesI.typD t)) with
                  | pSome p1 => 
                    fun pft1 => 
                      match p1 as x in base_typ 0 return p1 = x -> poption (ILogic.ILogicOps (TypesI.typD t)) with
                      | tString => 
                        fun pf'' =>
                          match @f_view typ (java_typ 0) TypeView_java_typ t2 as x 
                                return x = @f_view typ (java_typ 0) TypeView_java_typ t2 -> poption (ILogic.ILogicOps (TypesI.typD t)) with
                          | pSome p2 => 
                            fun pft1 => 
                              match p2 as x in java_typ 0 return p2 = x -> poption (ILogic.ILogicOps (TypesI.typD t)) with
                              | tVal =>
                                fun pf''' =>
                                  match @f_view typ (base_typ 0) TypeView_base_typ t3 as x 
                                        return x = @f_view typ (base_typ 0) TypeView_base_typ t3 -> poption (ILogic.ILogicOps (TypesI.typD t)) with
                                  | pSome p3 =>
                                    fun pf =>
                                      match p3 as x in base_typ 0 return p3 = x -> poption (ILogic.ILogicOps (TypesI.typD t)) with
                                      | tProp => fun pf' => pSome _
                                      | _ => fun _ => pNone
                                      end eq_refl
                                  | pNone => 
                                    fun _ =>
                                      match @f_view typ (java_typ 0) TypeView_java_typ t as x 
                                            return x = @f_view typ (java_typ 0) TypeView_java_typ t -> poption (ILogic.ILogicOps (TypesI.typD t)) with
                                      | pSome p3 =>
                                        fun pf =>
                                          match p3 as x in java_typ 0 return p3 = x -> poption (ILogic.ILogicOps (TypesI.typD t)) with
                                          | tAsn => fun _ => pSome _
                                          | _ => fun _ => pNone
                                          end eq_refl
                                      | pNone => fun _ => pNone
                                      end eq_refl
                                  end eq_refl
                              | _ => fun _ => pNone
                              end eq_refl
                          | pNone => fun _ => pNone
                          end eq_refl
                      | _ => fun _ => pNone
                      end eq_refl
                  | pNone => fun _ => pNone
                  end eq_refl
                | _ => fun _ => pNone
                end eq_refl
            end eq_refl
        end eq_refl).
      + subst; simpl in *; forward; inversion H1; subst; inversion pf; subst.
        pose proof (asNth_eq _ _ H0); subst; simpl; apply _.
      + subst; simpl in *; forward. inversion H3; subst; inversion pf; subst.
        pose proof (asNth_eq _ _ H0); subst; simpl; apply _.
      + subst; simpl in *; forward. inversion H3; subst; inversion pf; subst.
        pose proof (asNth_eq _ _ H0); subst; simpl; apply _.
      + subst; simpl in *; forward. 
        inversion pft1; inversion pft0; inversion H7; inversion pf; inversion H4; inversion H1;
        subst; simpl in *.
        pose proof (asNth_eq _ _ H6); pose proof (asNth_eq _ _ H0); pose proof (asNth_eq _ _ H3).
        subst; simpl. apply _.
      + subst; simpl in *; forward. 
Defined.

  Definition bilops : @bilogic_ops _ RType_typ.
  refine (
      fun t =>
        match @f_view typ (java_typ 0) TypeView_java_typ t as x 
              return x = @f_view typ (java_typ 0) TypeView_java_typ t -> poption (BILogic.BILOperators (TypesI.typD t)) with
        | pSome p =>
          fun pf =>
            match p as x in java_typ 0 return p = x -> poption (BILogic.BILOperators (TypesI.typD t)) with
            | tAsn => fun pfAsn => pSome _
            | _ => fun _ => pNone
            end eq_refl
        | pNone => 
          fun _ => 
            match t as x return t = x -> poption (BILogic.BILOperators (TypesI.typD t)) with
            | tyArr (tyArr t1 t2) t3 => 
              fun _ =>
                match @f_view typ (base_typ 0) TypeView_base_typ t1 as x 
                      return x = @f_view typ (base_typ 0) TypeView_base_typ t1 -> poption (BILogic.BILOperators (TypesI.typD t)) with
                | pSome p1 => 
                  fun pft1 => 
                    match p1 as x in base_typ 0 return p1 = x -> poption (BILogic.BILOperators (TypesI.typD t)) with
                    | tString => 
                      fun pf'' => 
                        match @f_view typ (java_typ 0) TypeView_java_typ t2 as x 
                              return x = @f_view typ (java_typ 0) TypeView_java_typ t2 -> poption (BILogic.BILOperators (TypesI.typD t)) with
                        | pSome p2 => 
                          fun pft1 => 
                            match p2 as x in java_typ 0 return p2 = x -> poption (BILogic.BILOperators (TypesI.typD t)) with
                            | tVal =>
                              fun pf''' => 
                                match @f_view typ (java_typ 0) TypeView_java_typ t as x 
                                      return x = @f_view typ (java_typ 0) TypeView_java_typ t -> poption (BILogic.BILOperators (TypesI.typD t)) with
                                | pSome p3 =>
                                  fun pf =>
                                    match p3 as x in java_typ 0 return p3 = x -> poption (BILogic.BILOperators (TypesI.typD t)) with
                                    | tAsn => fun _ => pSome _
                                    | _ => fun _ => pNone
                                    end eq_refl
                                | pNone => fun _ => pNone
                                end eq_refl 
                            | _ => fun _ => pNone
                            end eq_refl 
                        | _ => fun _ => pNone
                        end eq_refl 
                    | _ => fun _ => pNone
                    end eq_refl 
                | pNone => fun _ => pNone
                end eq_refl 
            | _ => fun _ => pNone
            end eq_refl 
        end eq_refl).
  + subst; simpl in *; forward; inversion H1; inversion pf; subst.
    pose proof (asNth_eq _ _ H0); subst; simpl; apply _.
  + subst; simpl in *; forward; inversion H1; inversion pf; subst.
Defined.

(*
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
*)
(*
Definition lops : @later_ops _ RType_typ :=
  fun t =>
    match t return option (ILLOperators (TypesI.typD t)) with
	  | tySpec => Some should_also_not_be_necessary
	  | _ => None
    end.
*)
(*
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
*)

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
(*
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
*)
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