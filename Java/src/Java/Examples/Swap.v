Require Import ChargeCore.Logics.ILogic.
Require Import ChargeCore.Logics.BILogic.
Require Import ChargeCore.Logics.ILEmbed.
Require Import ChargeCore.Open.Stack.

Require Import Java.Language.Lang.
Require Import Java.Language.Program.
Require Import Java.Semantics.AxiomaticSemantics.
Require Import Java.Semantics.OperationalSemantics.
Require Import Java.Logic.AssertionLogic.
Require Import Java.Logic.SpecLogic.
Require Import Java.Func.Reify.
Require Import Java.Func.JavaFunc.
Require Import Java.Func.Type.
Require Import Java.Tactics.SymEx.
Require Import Java.Tactics.Tactics.

Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Numbers.BinNums.
Require Import ExtLib.Structures.Applicative.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.Lambda.ExprDsimul.
Require Import ChargeCore.Open.OpenILogic.

Open Scope string.

Local Instance Applicative_Fun : Applicative (RFun (String.string -> val)) := 
{ pure := fun _ x _ => x
; ap := fun _ _ f x y => (f y) (x y)
}.

(* Swap represents type Swap *)
Module Swap.
Definition x : field := "x".
Definition y : field := "y".

Definition C : string := "Swap"%string.
Definition T : Type := (val * val).
Definition Swap := (fun p xy => (pointsto p x (fst xy)) ** (pointsto p y (snd xy))).

(* Start of specifications for set_int_int_void known as set_int_int_void *)

(* set_int_int_void body *)
Definition set_int_int_void_function := fun (t:T) (x:val) (y:val) => ((x,y),nothing).

Definition set_int_int_void_body :=
	(cseq (cwrite ("this")%string ("x")%string (E_var ("x_new")%string)) (cwrite ("this")%string ("y")%string (E_var ("y_new")%string))).

Definition nothing := (vint 0).

(* set_int_int_void definition *)
Definition set_int_int_void_method :=
	(Build_Method (("this")%string :: (("x_new")%string :: (("y_new")%string :: nil))) set_int_int_void_body (E_val nothing)).

(* Specification for set_int_int_void *)
Definition set_int_int_void_requires (t : (val * val)) : sasn :=
	ltrue ** (ap (ap (pure (T := RFun (String.string -> val)) Swap) (stack_get ("this")%string)) (pure (T := RFun (String.string -> val)) t)).

(* Specification for set_int_int_void *)
Definition set_int_int_void_ensures : sasn :=
	ltrue ** (ap (ap (pure (T := RFun (String.string -> val)) Swap) (stack_get ("this")%string)) (ap (ap (pure (T := RFun (String.string -> val)) pair) (stack_get ("x_new")%string)) (stack_get ("y_new")%string))).

(* set_int_int_void specification *)
Definition set_int_int_void_spec : spec :=
	Forall t : (val * val), (method_spec (C)%string ("set_int_int_void")%string (("this")%string :: (("x_new")%string :: (("y_new")%string :: nil))) ("")%string (set_int_int_void_requires t) (set_int_int_void_ensures //\\ ltrue)).

(* Start of specifications for swap_void known as swap_void *)

(* swap_void body *)
Definition swap_void_function := fun xy:T => ((snd (xy),fst (xy)), nothing).

Definition swap_void_body :=
	(cseq (cread ("x_old")%string ("this")%string ("x")%string) (cseq (cread ("y_old")%string ("this")%string ("y")%string) (cseq (cwrite ("this")%string ("x")%string (E_var ("y_old")%string)) (cwrite ("this")%string ("y")%string (E_var ("x_old")%string))))).

(* swap_void definition *)
Definition swap_void_method :=
	(Build_Method (("this")%string :: nil) swap_void_body (E_val nothing)).

(* Specification for swap_void *)
Definition swap_void_requires (x : (val)) (y : (val)) : sasn :=
	ltrue ** (ap (ap (pure (T := RFun (String.string -> val)) Swap) (stack_get ("this")%string)) (ap (ap (pure (T := RFun (String.string -> val)) pair) (pure (T := RFun (String.string -> val)) x)) (pure (T := RFun (String.string -> val)) y))).

(* Specification for swap_void *)
Definition swap_void_ensures (x : (val)) (y : (val)) : sasn :=
	ltrue ** (ap (ap (pure (T := RFun (String.string -> val)) Swap) (stack_get ("this")%string)) (ap (ap (pure (T := RFun (String.string -> val)) pair) (pure (T := RFun (String.string -> val)) y)) (pure (T := RFun (String.string -> val)) x))).

(* swap_void specification *)
Definition swap_void_spec : spec :=
	Forall x : (val), Forall y : (val), (method_spec (C)%string ("swap_void")%string (("this")%string :: nil) ("")%string (swap_void_requires x y) (swap_void_ensures x y //\\ ltrue)).

(* Class spec for Swap *)
Definition Class_spec :=
	(Build_Class (("x")%string :: (("y")%string :: nil)) ((("set_int_int_void")%string, set_int_int_void_method) :: ((("swap_void")%string, swap_void_method) :: nil))).

End Swap.

Definition Swap_prog :=
	(Build_Program (((Swap.C)%string, Swap.Class_spec) :: nil)).
 
 
Module Theorems.

Instance fs : Environment := 
  Build_Environment (FMapPositive.PositiveMap.empty (SymEnv.function typ _)).

(* set_int_int_void correctness lemma *)
Opaque ap.
Opaque pure.

Lemma set_int_int_void_correct : prog_eq Swap_prog |-- Swap.set_int_int_void_spec.
Proof.
  unfold Swap.set_int_int_void_spec.
  unfold Swap.set_int_int_void_requires.
  unfold Swap.set_int_int_void_ensures.
  unfold Swap.Swap.
  apply lforallR.
  intros t.
  unfold_method_spec.
  revert t.
  run_rtac reify_java term_table substTac2_sound.
Qed.

(* swap_void correctness lemma *)
Lemma swap_void_correct : prog_eq Swap_prog |-- Swap.swap_void_spec.
Proof.  
  unfold Swap.swap_void_spec.
  unfold method_spec.
  apply lforallR.
  intros.
  rename x into t_x.
  apply lforallR.
  intros.
  rename x into t_y.
  apply landR.
  - apply embedPropR.
    apply nodup_sound.
    reflexivity. 
  - apply lexistsR with (x := (("this")%string :: nil)).
    apply lexistsR with (x := (cseq (cread ("x_old")%string ("this")%string ("x")%string) (cseq (cread ("y_old")%string ("this")%string ("y")%string) (cseq (cwrite ("this")%string ("x")%string (E_var ("y_old")%string)) (cwrite ("this")%string ("y")%string (E_var ("x_old")%string)))))).
    apply lexistsR with (x := E_val nothing).
 	apply landR.
    + apply prog_eq_to_prop.
      split.
      * unfold method_lookup.
        exists Swap.Class_spec.
        split.
        -- simpl. left. reflexivity.
        -- simpl. right. left. unfold Swap.swap_void_method. unfold Swap.swap_void_body. reflexivity.
      * split.
        -- reflexivity.
        -- unfold not. intros. simpl in *. intuition congruence.
    + admit.  
Admitted.

(* Swap correctness theorem *)
Theorem Swap_correct : prog_eq Swap_prog |-- Swap.set_int_int_void_spec //\\ Swap.swap_void_spec.
Proof.
Admitted.

End Theorems.

