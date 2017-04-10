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
Require Import Java.Func.Reify.
Require Import Java.Func.JavaFunc.
Require Import Java.Func.Type.
Require Import Java.Tactics.SymEx.
Require Import Java.Tactics.Tactics.

Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ExtLib.Structures.Applicative.
Require Import MirrorCore.TypesI.
Require Import ChargeCore.Open.OpenILogic.

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
  Build_Method ("this"::"x"::nil) cons_body (E_val null).

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
                         

Local Instance Applicative_Fun : Applicative (RFun (string -> val)) :=
{ pure := fun _ x _ => x
; ap := fun _ _ f x y => (f y) (x y)
}.

Definition head_frame x xs : sasn :=
  (ap (ap (pure (T := RFun (string -> val)) List) 
          (stack_get "this")) 
      (pure  (T := RFun (string -> val)) (x::xs))).
Definition head_return x : sasn := 
    (embed (open_eq (stack_get "r") (pure (T := RFun (string -> val)) x))).
Definition head_requires x xs := head_frame x xs.
Definition head_ensures x xs := head_frame x xs.

Definition head_spec : spec :=
  Forall x : val, Forall xs : list val, 
    method_spec "List" "head" ("this"::nil) "r"
                (head_requires x xs)
                (head_ensures x xs //\\ head_return x).



Definition tail_frame h n : sasn :=
  ap (ap (ap (pure (T := RFun (string -> val)) pointsto) 
             (stack_get "this"))
         (pure (T := RFun (string -> val)) "head"))
     (pure (T := RFun (string -> val)) h) ** 
  ap (ap (ap (pure (T := RFun (string -> val)) pointsto) 
             (pure (T := RFun (string -> val)) h))
         (pure (T := RFun (string -> val)) "next"))
     (pure (T := RFun (string -> val)) n).
Definition tail_return n : sasn := 
    (embed (open_eq (stack_get "r") (pure (T := RFun (string -> val)) n))).
Definition tail_requires h n xs : sasn :=
  tail_frame h n **
  ap (ap (pure (T := RFun (string -> val)) Node) 
         (stack_get "this"))
     (pure  (T := RFun (string -> val)) xs).
Definition tail_ensures h n xs : sasn :=
  tail_frame h n **
  ap (ap (pure (T := RFun (string -> val)) List) 
          (stack_get "this")) 
     (pure  (T := RFun (string -> val)) xs).

Definition tail_spec : spec :=
  Forall h : val, Forall n : val, Forall xs : list val, 
    method_spec "List" "tail" ("this"::nil) "r"
                (tail_requires h n xs)
                (tail_ensures h n xs //\\ tail_return n).



Definition cons_requires xs : sasn :=
  ap (ap (pure (T := RFun (string -> val)) List) 
         (stack_get "this")) 
     (pure  (T := RFun (string -> val)) xs).
Definition cons_ensures xs : sasn :=
  ap (ap (pure List) 
         (stack_get "this")) 
     (ap (ap (pure cons) 
             (stack_get "n")) 
         (pure (T := RFun (string -> val)) xs)).
                                            
Definition cons_spec : spec :=
    Forall xs : list val, 
      method_spec "List" "cons" ("this"::"n"::nil) "" 
                  (cons_requires xs)
                  (cons_ensures xs).



Definition reverse_requires xs : sasn :=
  ap (ap (pure (T := RFun (string -> val)) List) 
         (stack_get "this")) 
     (pure  (T := RFun (string -> val)) xs).
Definition reverse_ensures xs : sasn :=
  ap (ap (pure (T := RFun (string -> val)) List) 
         (stack_get "this")) 
     (pure  (T := RFun (string -> val)) (rev xs)).

Definition reverse_spec : spec :=
    Forall xs : list val, 
      method_spec "List" "reverse" ("this"::nil) "" 
                  (reverse_requires xs)
                  (reverse_ensures xs).

Lemma unfold_method_spec (C : class) (m : string) 
  (pn pn' : list Lang.var) (rn : Lang.var) (Pr : Program) P Q c re S
  (HS : S |-- prog_eq Pr)
  (HNoDup : NoDup (rn::pn)) 
  (HSpec : method_lookup Pr C m {| m_params := pn'; m_body := c; m_ret := re |}) 
  (Hlength : Datatypes.length pn = Datatypes.length pn') 
  (Hmodify : forall x : Lang.var, In x pn' -> ~ In x (modifies c)) 
  (Htriple : S |-- triple (Subst.apply_subst P
          (Subst.substl_trunc (combine pn (map Open.var_expr pn')))) 
          (Subst.apply_subst Q
          (Subst.substl_trunc
            (combine (rn :: pn) (eval re :: map Open.var_expr pn')))) c) : 
   S |-- method_spec C m pn rn P Q.
Proof.
  unfold method_spec.
  repeat (apply lforallR; intros).
  apply landR. 
  apply embedPropR; assumption.
  apply (lexistsR pn').
  apply (lexistsR c).
  apply (lexistsR re).
  apply landR.
  etransitivity; [apply HS|]; apply prog_eq_to_prop.
  repeat split; assumption.
  assumption.
Qed.

Ltac solve_NoDup :=
  repeat (apply NoDup_cons; simpl); 
    first [intuition congruence | apply NoDup_nil].

Ltac solve_method_lookup :=
  unfold method_lookup; eexists; split; simpl; [
    intuition congruence|]; simpl; intuition congruence.
    
Ltac solve_subst :=
  run_rtac reify_java term_table substTac2_sound.

Opaque embed.
Opaque ap.
Opaque pure.

Instance fs : Environment := 
  Build_Environment (FMapPositive.PositiveMap.empty (SymEnv.function typ _)).


Lemma TailCorrect : prog_eq ListProg |-- tail_spec.
Proof.
  unfold tail_spec. unfold tail_requires. 
  unfold tail_ensures. unfold tail_return.
  repeat (apply lforallR; intros).
  eapply unfold_method_spec; [
    reflexivity |
    solve_NoDup |
    solve_method_lookup |
    simpl; reflexivity |
    simpl; intuition congruence |
    simpl
  ].
    unfold tail_frame.
    unfold Lang.var.
    revert x; revert x0; revert x1.
    solve_subst.
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

