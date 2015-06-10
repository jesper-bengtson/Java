Require Import Java.Tactics.SymEx.
Require Import Java.Tactics.Tactics.
Require Import Java.Logic.SpecLogic.
Require Import Java.Logic.AssertionLogic.
Require Import Java.Language.Lang.
Require Import Java.Semantics.OperationalSemantics.
Require Import Java.Func.Reify.
Require Import Java.Func.JavaFunc.


Require Import Charge.Logics.ILogic.
Require Import Charge.SetoidRewrite.Base.

Global Instance EmptyEnv : Environment := {
  java_env := SymEnv.from_list nil
}.


Lemma test_skip_lemma3 : testSkip 1.
Proof.
  unfold testSkip; simpl.
  run_rtac_print_code reify_imp term_table (@runTac_sound EmptyEnv rw_fail).
  admit.
  
Admitted.
