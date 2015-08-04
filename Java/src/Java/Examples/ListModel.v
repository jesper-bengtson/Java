Require Import Java.Semantics.AxiomaticSemantics.
Require Import Java.Logic.AssertionLogic.
Require Import Java.Language.Lang.

Require Import ChargeCore.Open.Stack.
Require Import ChargeCore.Logics.ILogic.
Require Import ChargeCore.Logics.ILEmbed.
Require Import ChargeCore.Logics.BILogic.
Require Import ChargeCore.Logics.BILogic.

Require Import Coq.Strings.String.
Require Import ZArith Coq.Lists.List.

Set Implicit Arguments.
Unset Strict Implicit.

Open Scope string_scope.
Open Scope list_scope.

Fixpoint NodeList (p : val) (xs : list val) : asn :=
  match xs with
    | nil => (p = null) /\\ ltrue
    | x::xs  => Exists v : val, pointsto p "val" x ** pointsto p "next" v ** NodeList v xs
  end.

Definition List (p : val) (xs : list val) : asn :=
  Exists h : val, pointsto p "head" h ** NodeList h xs.