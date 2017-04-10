Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Data.POption.
Require Import ExtLib.Tactics.

Require Import MirrorCore.TypesI.
Require Import MirrorCore.CTypes.CoreTypes.
Require Import MirrorCore.Views.FuncView.
Require Import MirrorCore.Views.Ptrns.
Require Import MirrorCore.Views.TypeView.
Require Import MirrorCore.Lib.StringView.
Require Import MirrorCore.Reify.ReifyClass.

Require Import ChargeCore.Open.Subst.

Require Import Java.Logic.AssertionLogic.
Require Import Java.Logic.SpecLogic.
Require Import Java.Language.Lang.
Require Import Java.Language.Program.

Set Implicit Arguments.
Set Strict Implicit.

Inductive java_typ : nat -> Set :=
| tVal : java_typ 0
| tSpec : java_typ 0
| tAsn : java_typ 0
| tProg : java_typ 0
| tMethod : java_typ 0
| tMethodName : java_typ 0
| tFieldName : java_typ 0
| tClassName : java_typ 0
| tCmd : java_typ 0
| tDExpr : java_typ 0.

Definition java_typ_dec {n} (a : java_typ n) : forall b, {a = b} + {a <> b}.
  refine(
    match a as a in java_typ n return forall b : java_typ n, {a = b} + {a <> b} with
    | tVal =>
      fun b =>
        match b as b in java_typ 0 return {tVal = b} + {tVal <> b} with
        | tVal => left eq_refl
        | _ => right (fun pf => _)
        end
    | tSpec =>
      fun b =>
        match b as b in java_typ 0 return {tSpec = b} + {tSpec <> b} with
        | tSpec => left eq_refl
        | _ => right (fun pf => _)
        end
    | tAsn =>
      fun b =>
        match b as b in java_typ 0 return {tAsn = b} + {tAsn <> b} with
        | tAsn => left eq_refl
        | _ => right (fun pf => _)
        end
    | tProg =>
      fun b =>
        match b as b in java_typ 0 return {tProg = b} + {tProg <> b} with
        | tProg => left eq_refl
        | _ => right (fun pf => _)
        end
    | tMethod =>  
      fun b =>
        match b as b in java_typ 0 return {tMethod = b} + {tMethod <> b} with
        | tMethod => left eq_refl
        | _ => right (fun pf => _)
        end
    | tMethodName =>  
      fun b =>
        match b as b in java_typ 0 return {tMethodName = b} + {tMethodName <> b} with
        | tMethodName => left eq_refl
        | _ => right (fun pf => _)
        end
    | tFieldName =>  
      fun b =>
        match b as b in java_typ 0 return {tFieldName = b} + {tFieldName <> b} with
        | tFieldName => left eq_refl
        | _ => right (fun pf => _)
        end
    | tClassName =>  
      fun b =>
        match b as b in java_typ 0 return {tClassName = b} + {tClassName <> b} with
        | tClassName => left eq_refl
        | _ => right (fun pf => _)
        end
    | tCmd =>
      fun b =>
        match b as b in java_typ 0 return {tCmd = b} + {tCmd <> b} with
        | tCmd => left eq_refl
        | _ => right (fun pf => _)
        end
    | tDExpr =>
      fun b =>
        match b as b in java_typ 0 return {tDExpr = b} + {tDExpr <> b} with
        | tDExpr => left eq_refl
        | _ => right (fun pf => _)
        end
    end);  clear -pf; inversion pf.
Defined.

Definition java_typD {n} (t : java_typ n) : type_for_arity n :=
  match t with
  | tVal => val
  | tSpec => spec
  | tAsn => asn
  | tProg => Program
  | tMethod => Method
  | tMethodName => method
  | tFieldName => method
  | tClassName => class
  | tCmd => cmd
  | tDExpr => dexpr
  end.

Section DepMatch_java_typ.
  Context {typ : Set}.
  Context {RType_typ : RType typ}.
  Context {FV : PartialView typ (java_typ 0)}.
  Context {FVOk : TypeViewOk typD (java_typD (n := 0)) FV}.

  Definition val_match (F : typ -> Type) (x : typ) :
    F (f_insert tVal) -> (unit -> F x) -> F x :=
    match f_view x as Z return f_view x = Z -> F (f_insert tVal) -> (unit -> F x) -> F x
    with
    | pSome v =>
      match v as y in java_typ 0 return f_view x = pSome y ->
                                        F (f_insert tVal) ->
                                        (unit -> F x) -> F x with
      | tVal =>
        fun pf X _ =>
          match (match @pv_ok _ _ _ _ FVOk x tVal with | conj A _ => A end) pf
                in _ = Z
                return F Z with
          | eq_refl => X
          end
      | _ => fun _ _ X => X tt
      end
    | pNone => fun _ _ X => X tt
    end eq_refl.

  Definition asn_match (F : typ -> Type) (x : typ) :
    F (f_insert tAsn) -> (unit -> F x) -> F x :=
    match f_view x as Z return f_view x = Z -> F (f_insert tAsn) -> (unit -> F x) -> F x
    with
    | pSome v =>
      match v as y in java_typ 0 return f_view x = pSome y ->
                                        F (f_insert tAsn) ->
                                        (unit -> F x) -> F x with
      | tAsn =>
        fun pf X _ =>
          match (match @pv_ok _ _ _ _ FVOk x tAsn with | conj A _ => A end) pf
                in _ = Z
                return F Z with
          | eq_refl => X
          end
      | _ => fun _ _ X => X tt
      end
    | pNone => fun _ _ X => X tt
    end eq_refl.

  Definition spec_match (F : typ -> Type) (x : typ) :
    F (f_insert tSpec) -> (unit -> F x) -> F x :=
    match f_view x as Z return f_view x = Z -> F (f_insert tSpec) -> (unit -> F x) -> F x
    with
    | pSome v =>
      match v as y in java_typ 0 return f_view x = pSome y ->
                                        F (f_insert tSpec) ->
                                        (unit -> F x) -> F x with
      | tSpec =>
        fun pf X _ =>
          match (match @pv_ok _ _ _ _ FVOk x tSpec with | conj A _ => A end) pf
                in _ = Z
                return F Z with
          | eq_refl => X
          end
      | _ => fun _ _ X => X tt
      end
    | pNone => fun _ _ X => X tt
    end eq_refl.

End DepMatch_java_typ.

Section FuncView_java_type.
  Context {typ : Set}.
  Context {FV : PartialView typ (java_typ 0)}.

  Definition tyVal := f_insert tVal.
  Definition tySpec := f_insert tSpec.
  Definition tyAsn := f_insert tAsn.
  Definition tyProg := f_insert tProg.
  Definition tyMethod := f_insert tMethod.
  Definition tyMethodName := f_insert tMethodName.
  Definition tyFieldName := f_insert tFieldName.
  Definition tyClassName := f_insert tClassName.
  Definition tyCmd := f_insert tCmd.
  Definition tyDExpr := f_insert tDExpr.

  Definition fptrn_tyVal : ptrn (java_typ 0) unit :=
    fun f U good bad =>
      match f with
        | tVal => good tt
        | _ => bad f
      end.

  Definition fptrn_tySpec : ptrn (java_typ 0) unit :=
    fun f U good bad =>
      match f with
        | tSpec => good tt
        | _ => bad f
      end.

  Definition fptrn_tyAsn : ptrn (java_typ 0) unit :=
    fun f U good bad =>
      match f with
        | tAsn => good tt
        | _ => bad f
      end.

  Definition fptrn_tyProg : ptrn (java_typ 0) unit :=
    fun f U good bad =>
      match f with
        | tProg => good tt
        | _ => bad f
      end.

  Definition fptrn_tyMethod : ptrn (java_typ 0) unit :=
    fun f U good bad =>
      match f with
        | tMethod => good tt
        | _ => bad f
      end.

  Definition fptrn_tyMethodName : ptrn (java_typ 0) unit :=
    fun f U good bad =>
      match f with
        | tMethodName => good tt
        | _ => bad f
      end.

  Definition fptrn_tyClassName : ptrn (java_typ 0) unit :=
    fun f U good bad =>
      match f with
        | tClassName => good tt
        | _ => bad f
      end.

  Definition fptrn_tyFieldName : ptrn (java_typ 0) unit :=
    fun f U good bad =>
      match f with
        | tFieldName => good tt
        | _ => bad f
      end.

  Definition fptrn_tyCmd : ptrn (java_typ 0) unit :=
    fun f U good bad =>
      match f with
        | tCmd => good tt
        | _ => bad f
      end.

  Definition fptrn_tyDExpr : ptrn (java_typ 0) unit :=
    fun f U good bad =>
      match f with
        | tDExpr => good tt
        | _ => bad f
      end.

  Global Instance ptrn_tyVal_ok : ptrn_ok fptrn_tyVal.
  Proof.
    red; intros.
    unfold fptrn_tyVal.
    unfold Succeeds; unfold Fails.
    destruct x; [left; exists tt; reflexivity|..]; right; reflexivity.
  Qed.

  Global Instance ptrn_tySpec_ok : ptrn_ok fptrn_tySpec.
  Proof.
    red; intros.
    unfold fptrn_tySpec.
    unfold Succeeds; unfold Fails.
    destruct x; try (right; reflexivity).
    left; exists tt; reflexivity.
  Qed.

  Global Instance ptrn_tyAsn_ok : ptrn_ok fptrn_tyAsn.
  Proof.
    red; intros.
    unfold fptrn_tyAsn.
    unfold Succeeds; unfold Fails.
    destruct x; try (right; reflexivity).
    left; exists tt; reflexivity.
  Qed.

  Global Instance ptrn_tyProg_ok : ptrn_ok fptrn_tyProg.
  Proof.
    red; intros.
    unfold fptrn_tyProg.
    unfold Succeeds; unfold Fails.
    destruct x; try (right; reflexivity).
    left; exists tt; reflexivity.
  Qed.

  Global Instance ptrn_tyMethod_ok : ptrn_ok fptrn_tyMethod.
  Proof.
    red; intros.
    unfold fptrn_tyMethod.
    unfold Succeeds; unfold Fails.
    destruct x; try (right; reflexivity).
    left; exists tt; reflexivity.
  Qed.

  Global Instance ptrn_tyCmd_ok : ptrn_ok fptrn_tyCmd.
  Proof.
    red; intros.
    unfold fptrn_tyCmd.
    unfold Succeeds; unfold Fails.
    destruct x; try (right; reflexivity).
    left; exists tt; reflexivity.
  Qed.

  Global Instance ptrn_tyDExpr_ok : ptrn_ok fptrn_tyDExpr.
  Proof.
    red; intros.
    unfold fptrn_tyDExpr.
    unfold Succeeds; unfold Fails.
    destruct x; try (right; reflexivity).
    left; exists tt; reflexivity.
  Qed.

  Definition ptrn_tyVal : ptrn typ unit := ptrn_view FV fptrn_tyVal.
  Definition ptrn_tySpec : ptrn typ unit := ptrn_view FV fptrn_tySpec.
  Definition ptrn_tyAsn : ptrn typ unit := ptrn_view FV fptrn_tyAsn.
  Definition ptrn_tyProg : ptrn typ unit := ptrn_view FV fptrn_tyProg.
  Definition ptrn_tyMethod : ptrn typ unit := ptrn_view FV fptrn_tyMethod.
  Definition ptrn_tyMethodName : ptrn typ unit := ptrn_view FV fptrn_tyMethodName.
  Definition ptrn_tyClassName : ptrn typ unit := ptrn_view FV fptrn_tyClassName.
  Definition ptrn_tyFieldName : ptrn typ unit := ptrn_view FV fptrn_tyFieldName.
  Definition ptrn_tyCmd : ptrn typ unit := ptrn_view FV fptrn_tyCmd.
  Definition ptrn_tyDExpr : ptrn typ unit := ptrn_view FV fptrn_tyDExpr.

End FuncView_java_type.

Section RelDec_java_type.

  Global Instance RelDec_java_typ (x : nat) : RelDec (@eq (java_typ x)) := {
    rel_dec a b :=
      match java_typ_dec a b with
      | left _ => true
      | right _ => false
      end
  }.

  Global Instance RelDecOk_java_typ (x : nat) : RelDec_Correct (RelDec_java_typ x).
  Proof.
    split; intros.
    unfold rel_dec; simpl.
    remember (java_typ_dec x0 y).
    destruct s; subst; intuition.
  Qed.

End RelDec_java_type.

Section TSym_java_type.

  Global Instance TSym_java_typ : TSym java_typ := {
    symbolD n := java_typD (n := n);
    symbol_dec n := java_typ_dec (n := n)
  }.

End TSym_java_type.

Section ReifyJavaType.
  Context {typ : Set} {FV : PartialView typ (java_typ 0)}.
  Context {RType_typ : RType typ} {Typ2_Fun : Typ2 _ Fun}.
  Context {Typ0_string : Typ0 _ String.string}.

  Let tyArr := @typ2 _ RType_typ _ _.
  Let tyString := @typ0 _ RType_typ _ _.

  Definition reify_tyVar : Command typ :=
    CPattern (ls := nil) (RExact Lang.var) tyString.

  Definition reify_tyVal : Command typ :=
    CPattern (ls := nil) (RExact val) (@tyVal typ _).

  Definition reify_tyStack : Command typ :=
    CPattern (ls := nil) (RExact Lang.stack) (tyArr tyString tyVal).

  Definition reify_tyExpr : Command typ :=
    CPattern (ls := nil) (RExact (Open.expr (A := String.string) (val := val))) (tyArr (tyArr tyString tyVal) tyVal).

  Definition reify_tySpec : Command typ :=
    CPattern (ls := nil) (RExact spec) tySpec.

  Definition reify_tyAsn : Command typ :=
    CPattern (ls := nil) (RExact asn) tyAsn.

  Definition reify_tySasn : Command typ :=
    CPattern (ls := nil) (RExact sasn) (tyArr (tyArr tyString tyVal) tyAsn).

  Definition reify_tyProg : Command typ :=
    CPattern (ls := nil) (RExact Program) tyProg.

  Definition reify_tyMethod : Command typ :=
    CPattern (ls := nil) (RExact Method) tyMethod.

  Definition reify_tyMethodName : Command typ :=
    CPattern (ls := nil) (RExact method) tyMethodName.

  Definition reify_tyClassName : Command typ :=
    CPattern (ls := nil) (RExact class) tyClassName.

  Definition reify_tyFieldName : Command typ :=
    CPattern (ls := nil) (RExact field) tyFieldName.

  Definition reify_tyCmd : Command typ :=
    CPattern (ls := nil) (RExact cmd) tyCmd.

  Definition reify_tyDExpr : Command typ :=
    CPattern (ls := nil) (RExact dexpr) tyDExpr.

    Definition reify_java_typ : Command typ :=
      CFirst (reify_tyVal :: reify_tyStack :: reify_tySpec :: reify_tyAsn :: 
              reify_tyProg :: reify_tySasn :: reify_tyMethod :: reify_tyCmd :: 
              reify_tyMethodName :: reify_tyClassName :: reify_tyFieldName ::
              reify_tyExpr :: reify_tyDExpr :: reify_tyVar :: nil).

End ReifyJavaType.

Arguments reify_java_typ _ {_ _ _ _}.
