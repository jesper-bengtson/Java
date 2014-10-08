Require Import AxiomaticSemantics String AssertionLogic ILogic ILEmbed BILogic Lang Stack ZArith List ListModel.
Require Import Program SpecLogic OperationalSemantics.

Set Implicit Arguments.
Unset Strict Implicit.

Open Scope string_scope.
Open Scope cmd_scope.
Open Scope list_scope.

Definition add_body :=
  (cseq (calloc "tn" "NodeC")
        (cseq (cwrite "tn" "val" (E_var "n")) (* This n used to be cast to an integer *)
              (cseq (cread "lst" "this" "head")
                    (cseq (cwrite "tn" "next" (E_var "lst"))
                          (cwrite "this" "head" (E_var "tn")))))).

  Definition AddM : Method :=
    Build_Method ("this"::"n"::nil) add_body (E_val (vint 0)).

  Definition NodeC :=
    Build_Class ("val"::"next"::nil) nil.
  
  Definition ListC := Build_Class ("head"::nil) (("add", AddM)::nil).

  Definition ListProg := Build_Program
    (("List", ListC)::("NodeC", NodeC)::nil).  

  Definition add_spec : spec :=
    Forall xs : list Z, method_spec "List" "add" ("this"::"n"::nil) "" 
                                    (fun s => List (s "this") xs) 
                                    (fun s => List (s "this") ((val_to_int (s "n"))::xs)).

            
Lemma ListCorrect : prog_eq ListProg |-- add_spec.
Proof.
  admit.
Qed.
(*
  unfold add_spec.
  apply lforallR; intros xs.
  unfold add_spec.
  unfold ProgAux. unfold ListC, NodeC.
  
  apply landR.
  
  apply embedPropR. search_NoDup string_dec.
  do 3 eapply lexistsR.
  apply landR.
  Print prog_eq_to_prop.
  apply prog_eq_to_prop.
  unfold method_spec.
  Check Build_Class.
  unfold method_lookup.
  unfold Prog. simpl. ProgAux. simpl.
  unfold add_spec. unfold method_spec.
  apply lforallR; intros xs.
  apply landR.
  apply embedPropR.
  search_NoDup string_dec.

  do 3 eapply lexistsR. apply landR.
  apply prog_eq_to_prop.
  split.
  unfold method_lookup. simpl.
  eexists.
  unfold ListC.
  unfold Prog, ProgAux.
  simpl; split.
  SM'.mapsto_tac.
  SM'.mapsto_tac.
  split.
  reflexivity.
  unfold add_body. simpl.
  check_not_modifies.

  Require Import Subst.
  unfold apply_subst, stack_subst.
  simpl.
  unfold add_body.
  eapply rule_seq.
  eapply roc_pre with ltrue; [apply ltrueR|].
  etransitivity; [|apply rule_alloc_ax with (fields := SS.add "val" (SS.add "next" SS.empty))].
  apply prog_eq_to_prop.
  unfold Prog, ProgAux.
  simpl.
  eexists.
  split.
  SM'.mapsto_tac.
  reflexivity.
  rewrite <- exists_into_precond2.
  apply lforallR. intro p.

  
  simpl.
  admit.
Qed.
*)