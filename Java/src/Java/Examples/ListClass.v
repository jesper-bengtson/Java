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
Require Import Java.Examples.ListModel.

Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Set Implicit Arguments.
Unset Strict Implicit.

Open Scope string_scope.
Open Scope cmd_scope.
Open Scope list_scope.

Definition head_body :=
  (cseq (cread "h" "this" "head")
        (cread "v" "h" "value")).

Definition HeadM : Method :=
  Build_Method ("this"::nil) head_body (E_var "v").

Definition tail_body :=
  (cseq (calloc "lst" "List")
        (cseq (cread "h" "this" "head")
              (cseq (cread "tail" "h" "next")
                    (cwrite "lst" "head" (E_var "tail"))))).

Definition TailM : Method :=
  Build_Method ("this"::nil) tail_body (E_var "lst").

Definition cons_body :=
  (cseq (calloc "n" "Node")
        (cseq (cwrite "n" "val" (E_var "x")) 
              (cseq (cread "lst" "this" "head")
                    (cseq (cwrite "n" "next" (E_var "lst"))
                          (cwrite "this" "head" (E_var "n")))))).

Definition ConsM : Method :=
  Build_Method ("this"::"n"::nil) cons_body (E_val null).

Definition reverse_body :=
  (cseq (cread "i" "this" "head")
        (cseq (cassign "j" (E_val null))
              (cseq (cwhile (E_not (E_eq (E_var "i") (E_val null)))
                            (cseq (cread "k" "i" "next")
                                  (cseq (cwrite "i" "next" (E_var "j"))
                                        (cseq (cassign "j" (E_var "i"))
                                              (cassign "i" (E_var "k"))))))
                    (cwrite "this" "head" (E_var "j"))))).

Definition ReverseM : Method :=
  Build_Method ("this"::nil) reverse_body (E_val null).

Definition NodeC :=
  Build_Class ("val"::"next"::nil) nil.

Definition ListC := Build_Class ("head"::nil) (("head", HeadM) ::
                                               ("tail", TailM) ::
                                               ("cons", ConsM) ::
                                               ("reverse", ReverseM) ::
                                               nil).

Definition ListProg := Build_Program
                         (("List", ListC)::("Node", NodeC)::nil).  

Require Import ExtLib.Structures.Applicative.
Require Import MirrorCore.TypesI.
Require Import ChargeCore.Open.OpenILogic.

Local Instance Applicative_Fun : Applicative (RFun stack) :=
{ pure := fun _ x _ => x
; ap := fun _ _ f x y => (f y) (x y)
}.

Definition head_frame x xs : sasn :=
  (ap (ap (pure (T := RFun stack) List) 
          (stack_get "this")) 
      (pure  (T := RFun stack) (x::xs))).
Definition head_return x : sasn := 
    (embed (open_eq (stack_get "r") (pure (T := RFun stack) x))).
Definition head_requires x xs := head_frame x xs.
Definition head_ensures x xs := head_frame x xs.

Definition head_spec : spec :=
  Forall x : val, Forall xs : list val, 
    method_spec "List" "head" ("this"::nil) "r"
                (head_requires x xs)
                (head_ensures x xs //\\ head_return x).



Definition tail_frame h n : sasn :=
  ap (ap (ap (pure (T := RFun stack) pointsto) 
             (stack_get "this"))
         (pure (T := RFun stack) "head"))
     (pure (T := RFun stack) h) ** 
  ap (ap (ap (pure (T := RFun stack) pointsto) 
             (pure (T := RFun stack) h))
         (pure (T := RFun stack) "next"))
     (pure (T := RFun stack) n).
Definition tail_return n : sasn := 
    (embed (open_eq (stack_get "r") (pure (T := RFun stack) n))).
Definition tail_requires h n xs : sasn :=
  tail_frame h n **
  ap (ap (pure (T := RFun stack) Node) 
         (stack_get "this"))
     (pure  (T := RFun stack) xs).
Definition tail_ensures h n xs : sasn :=
  tail_frame h n **
  ap (ap (pure (T := RFun stack) List) 
          (stack_get "this")) 
     (pure  (T := RFun stack) xs).

Definition tail_spec : spec :=
  Forall h : val, Forall n : val, Forall x : val, Forall xs : list val, 
    method_spec "List" "tail" ("this"::nil) "r"
                (tail_requires h n xs)
                (tail_ensures h n xs //\\ tail_return n).



Definition cons_requires xs : sasn :=
  ap (ap (pure (T := RFun stack) List) 
         (stack_get "this")) 
     (pure  (T := RFun stack) xs).
Definition cons_ensures xs : sasn :=
  ap (ap (pure List) 
         (stack_get "this")) 
     (ap (ap (pure cons) 
             (stack_get "n")) 
         (pure (T := RFun stack) xs)).
                                            
Definition cons_spec : spec :=
    Forall xs : list val, 
      method_spec "List" "cons" ("this"::"n"::nil) "" 
                  (cons_requires xs)
                  (cons_ensures xs).



Definition reverse_requires xs : sasn :=
  ap (ap (pure (T := RFun stack) List) 
         (stack_get "this")) 
     (pure  (T := RFun stack) xs).
Definition reverse_ensures xs : sasn :=
  ap (ap (pure (T := RFun stack) List) 
         (stack_get "this")) 
     (pure  (T := RFun stack) (rev xs)).

Definition reverse_spec : spec :=
    Forall xs : list val, 
      method_spec "List" "reverse" ("this"::nil) "" 
                  (reverse_requires xs)
                  (reverse_ensures xs).
            
Lemma HeadCorrect : prog_eq ListProg |-- head_spec.
Proof.
  admit.
Admitted.

Lemma TailCorrect : prog_eq ListProg |-- tail_spec.
Proof.
  admit.
Admitted.

Lemma ConsCorrect : prog_eq ListProg |-- cons_spec.
Proof.
  admit.
Admitted.

Lemma ReverseCorrect : prog_eq ListProg |-- reverse_spec.
Proof.
  admit.
Admitted.

Lemma ListCorrect : prog_eq ListProg |-- head_spec //\\ tail_spec //\\ cons_spec //\\ reverse_spec.
Proof.
  admit.
Admitted.