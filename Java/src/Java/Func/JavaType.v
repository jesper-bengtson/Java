Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Data.POption.
Require Import ExtLib.Tactics.

Require Import MirrorCore.TypesI.
Require Import MirrorCore.MTypes.ModularTypes.
Require Import MirrorCore.Views.FuncView.

Require Import ChargeCore.Open.Subst.

Require Import Java.Logic.AssertionLogic.
Require Import Java.Logic.SpecLogic.
Require Import Java.Language.Lang.
Require Import Java.Language.Program.

Set Implicit Arguments.
Set Strict Implicit.

Universe U.

Inductive java_typ : nat -> Type@{U} :=
| tVal : java_typ 0
| tSpec : java_typ 0
| tAsn : java_typ 0
| tProg : java_typ 0
| tMethod : java_typ 0
| tCmd : java_typ 0
| tExpr : java_typ 0
| tSubst : java_typ 0.

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
    | tCmd =>
      fun b =>
        match b as b in java_typ 0 return {tCmd = b} + {tCmd <> b} with
        | tCmd => left eq_refl
        | _ => right (fun pf => _)
        end
    | tExpr =>
      fun b =>
        match b as b in java_typ 0 return {tExpr = b} + {tExpr <> b} with
        | tExpr => left eq_refl
        | _ => right (fun pf => _)
        end
    | tSubst =>
      fun b =>
        match b as b in java_typ 0 return {tSubst = b} + {tSubst <> b} with
        | tSubst => left eq_refl
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
  | tCmd => cmd
  | tExpr => dexpr
  | tSubst => @subst var val
  end.


Section FuncView_java_type.
  Context {typ : Type}.
  Context {FV : FuncView typ (java_typ 0)}.

  Definition tyVal := f_insert tVal.
  Definition tySpec := f_insert tSpec.
  Definition tyAsn := f_insert tAsn.
  Definition tyProg := f_insert tProg.
  Definition tyMethod := f_insert tMethod.
  Definition tyCmd := f_insert tCmd.
  Definition tyExpr := f_insert tExpr.
  Definition tySubst := f_insert tSubst.

End FuncView_java_type.