Require Import Program  Heap ProtocolLogic AssertionLogic OperationalSemantics SpecLogic Util Decidable.
Require Import MapInterface MapFacts List RelationClasses Setoid.
Require Import SepAlg SepAlgInsts ILInsts ILogic ILEmbed ILEmbedTac ILQuantTac OpenILogic
               SepAlgMap UUSepAlg Open Subst Stack Lang SemCmd HeapArr ST SemCmdRules BILogic BILInsts Rel.

Open Scope string_scope.

Fixpoint Node_list (p : val) (xs : list sval) : asn :=
  match xs with
    | nil => embed (p = null)
    | x :: xs => Exists v, Node_list v xs ** pointsto p "val" x ** pointsto p "next" v 
  end
.

Definition List_rep (p : val) (xs : list sval) : asn :=
  Exists head, Node_list head xs ** pointsto p "head" head.

Local Existing Instance DecSval.

Lemma Node_list_decidable (p : val) (xs : list sval) : DecidableAsn (Node_list p xs).
Proof.
  generalize dependent p.
  induction xs.
  * intros p Pr n h.
    destruct (dec_eq p null); [ left; apply e | right; intro Hfail; auto ].
  * intro p.
    assert (forall (p' : sval), DecidableAsn (@sepSP asn _ (Node_list p' xs) (pointsto p "val" a))).
      intros p'. specialize (IHxs p').
      apply pointsto_decidable_2 with (v := p) (f := "val") (e := a) in IHxs.
      exact IHxs.
    apply decidable_existsI with (p := p) (f := "next") in H.
    unfold Node_list; fold Node_list.
    setoid_rewrite <- sepSPA.
    exact H.
Qed.

Lemma List_rep_decidable (p : val) (xs : list sval) : DecidableAsn (List_rep p xs).
Proof.  
  unfold List_rep.
  apply decidable_existsI.
  intro p'; apply Node_list_decidable.
Qed.

Lemma List_rep_decidable_val (p : val) (xs : list sval) : DecidableSasn (`List_rep `p `xs).
Proof.
  intros s. unfold liftn, lift; simpl.
  apply List_rep_decidable.
Qed.

Lemma List_rep_decidable_var (p : var) (xs : list sval) : DecidableSasn (`List_rep p/V `xs).
Proof.
  intros s. unfold liftn, lift, var_expr; simpl.
  apply List_rep_decidable.
Qed.
