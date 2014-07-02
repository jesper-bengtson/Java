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




  Require Import ILInsts.


Program Fixpoint search_NoDup
    {A} (A_dec: forall a b: A, {a=b}+{a<>b}) (l: list A) : option (NoDup l) :=
  match l with
  | nil => Some _
  | a::l' =>
      match search_NoDup A_dec l' with
      | Some nodup =>
          match In_dec A_dec a l' with
          | left isin => None
          | right notin => Some _
          end
      | None => None
      end
  end.
Next Obligation.
intros. constructor.
Qed. Next Obligation.
intros. subst. constructor; assumption.
Defined.

(* Funny function borrowed from Chlipala's book *)
Definition option_proof {P: Prop} (pf': option P) :=
  match pf' return (match pf' with Some _ => P | None => True end) with
  | Some pf => pf
  | None => I
  end.

(* Tactic for applying a proof search procedure *)
Ltac search pf' := exact (option_proof pf') || fail "No proof found".

Ltac search_NoDup dec :=
  match goal with
  |- NoDup ?l => search (search_NoDup dec l)
  end.

Ltac check_not_modifies :=
    let x := fresh "y" in let HC := fresh "HC" in let HIn := fresh "HIn" in
      intros x HC HIn; simpl in *;
        repeat match goal with
                 | [ HIn: context [SS.In x (SS.union ?S1 ?S2)] |- _] =>
                   rewrite SS'.union_iff in HIn
                 | [ HIn: context [SS.In x (SS.add ?e ?S)] |- _] =>
                   rewrite SS'.add_iff in HIn
                 | [ HIn: context [SS.In x (SS.singleton ?e)] |- _] =>
                   rewrite SS'.singleton_iff in HIn
                 | [ HIn: context [SS.In x SS.empty] |- _] =>
                   rewrite SS'.empty_iff in HIn
               end; intuition (subst; discriminate).


Definition prog_eq Prog : spec := [prog] (fun P => P = Prog).

Lemma prog_eq_to_prop P (f : Prog_wf -> Prop) (H : f P) : prog_eq P |-- [prog] f.
Proof.
  Transparent ILPre_Ops.
  intros Q n HQ R HQR.
  specialize (HQ _ HQR).
  simpl in *. subst. apply H.
  Opaque ILPre_Ops.
Qed.

Lemma ListCorrect : prog_eq Prog|-- add_spec.
Proof.
  unfold add_spec. unfold method_spec.
  apply lforallR; intros xs.
  apply landR.
  apply embedPropR.
  search_NoDup string_dec.

  do 3 eapply lexistsR. apply landR.
  apply prog_eq_to_prop.
  split.
  eexists.
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