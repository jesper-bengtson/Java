Add Rec LoadPath "/Users/jebe/git/Java/Java/bin".
Add Rec LoadPath "/Users/jebe/git/Charge/Charge!/bin".
Add Rec LoadPath "/Users/jebe/coq/user-contrib/Containers" as Containers.

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
    Build_Class (SS.add "val" (SS.add "next" SS.empty)) (SM.empty _).
  
  Definition ListC := Build_Class (SS.add "head" SS.empty) (SM.add "add" AddM (SM.empty _)).

  Definition ProgAux := Build_Program
    (SM.add "List" ListC (SM'.singleton "NodeC" NodeC)).

  Program Definition Prog := @Build_Prog_wf ProgAux _ .
  Next Obligation.
    admit. (* I think we have automation for this *)
  Qed.
  

  Definition add_spec : spec :=
    Forall xs : list Z, method_spec "List" "add" ("this"::"n"::nil) "" 
                                    (fun s => List (s "this") xs) 
                                    (fun s => List (s "this") ((val_to_int (s "n"))::xs)).




Lemma ListCorrect : [prog] (fun P => P = Prog) |-- add_spec.
Proof.
  unfold add_spec, method_spec.
  apply lforallR; intros xs.
  apply landR.
  admit. (* Get back to this, but trivial *)
  apply lexistsR with ("this"::"n"::nil).
  apply lexistsR with add_body.
  apply lexistsR with (E_val (vint 0)).
  apply landR. admit. (* lookup in the maps *)
  simpl.
  Require Import Subst.
  unfold apply_subst, stack_subst.
  simpl.
  unfold add_body.
  
  eapply rule_seq.
  Check rule_alloc_ax.
  eapply roc_pre with ltrue; [apply ltrueR|].
  etransitivity; [|apply rule_alloc_ax with (fields := SS.add "val" (SS.add "next" SS.empty))].
  admit. (* Automation missing *)

  eapply rule_seq.


  simpl.

  