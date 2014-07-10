Require Import AxiomaticSemantics String AssertionLogic.
Require Import ILogic ILEmbed.
Require Import Charge.Logics.BILogic Lang Stack ZArith List.

Set Implicit Arguments.
Unset Strict Implicit.

Open Scope string_scope.
Open Scope list_scope.

  Fixpoint NodeList (p : val) (xs : list Z) : asn :=
    match xs with
      | nil => (p = null) /\\ ltrue
      | x::xs  => Exists v : val, pointsto p "val" x ** pointsto p "next" v ** NodeList v xs
    end.

  Definition List (p : val) (xs : list Z) : asn :=
    Exists h : val, pointsto p "head" h ** NodeList h xs.