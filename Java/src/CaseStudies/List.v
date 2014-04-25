Require Import Program  Heap ProtocolLogic AssertionLogic OperationalSemantics SpecLogic Util Decidable.
Require Import MapInterface MapFacts List RelationClasses Setoid OrderedTypeEx.
Require Import SepAlg SepAlgInsts ILInsts ILogic ILEmbed ILEmbedTac ILQuantTac OpenILogic
               SepAlgMap UUSepAlg Open Subst Stack Lang SemCmd HeapArr ST SemCmdRules BILogic BILInsts Rel.

Open Scope string_scope.
Local Existing Instance DecSval.

Fixpoint Node_list (p : val) (xs : list sval) : asn :=
  match xs with
    | nil => embed (p = null)
    | x :: xs => Exists v, pointsto p "val" x ** pointsto p "next" v ** Node_list v xs  
  end
.

Definition List_rep (p : val) (xs : list sval) : asn :=
  Exists head, pointsto p "head" head ** Node_list head xs .

Lemma Node_list_decidable (p : val) (xs : list sval) : DecidableAsn (Node_list p xs).
Proof.
  generalize dependent p; induction xs.
  * intros p Pr n h.
    destruct (dec_eq p null); [ left; apply e | right; intro Hfail; auto ].
  * intro p.
    assert (forall (p' : sval), DecidableAsn (@sepSP asn _ (Node_list p' xs) (pointsto p "val" a))) by
      (intros p'; apply pointsto_decidable_2; apply IHxs). 
    apply decidable_existsI with (p := p) (f := "next") in H.
    setoid_rewrite sepSPA in H; setoid_rewrite <- sepSPC in H; setoid_rewrite sepSPA in H.
    apply H.
Qed.

Lemma List_rep_decidable (p : val) (xs : list sval) : DecidableAsn (List_rep p xs).
Proof.
  unfold List_rep; setoid_rewrite sepSPC.
  apply decidable_existsI.
  intro p'; apply Node_list_decidable.
Qed.

Lemma List_rep_decidable_val (p : val) (xs : list sval) : DecidableSasn (`List_rep `p `xs).
Proof. intros s; unfold liftn, lift; simpl; apply List_rep_decidable. Qed.

Lemma List_rep_decidable_var (p : var) (xs : list sval) : DecidableSasn (`List_rep p/V `xs).
Proof. intros s; unfold liftn, lift, var_expr; simpl; apply List_rep_decidable. Qed.

Inductive List_sorted : list sval -> Prop :=
  | Ls_nil    : List_sorted nil
  | Ls_single : forall (a : sval), List_sorted (a :: nil)
  | Ls_cons   : forall (a1 a2 : sval) (l : list sval), 
                List_sorted (a2 :: l) -> val_to_nat a1 < val_to_nat a2 -> List_sorted (a1 :: a2 :: l) 
  .
Definition List_elements_equal (l1 l2 : list sval) : Prop := forall (e : sval), List.In e l1 <-> List.In e l2.
Program Definition Sorted_of (l1 l2 : list sval) : Prop := List_elements_equal l1 l2 //\\ List_sorted l2.

Local Transparent EmbedAsnPropOp.
Local Transparent EmbedILPreDropOp.
Lemma List_sorted_decidable (l : list sval) : DecidableAsn (embed (List_sorted l)).
Proof.
  intros Pr n h; simpl.
  induction l; [left; constructor |].
  destruct l; [left; constructor |].
  destruct IHl; [| right; intro Hfail; apply H; inversion Hfail; assumption].
  destruct (lt_dec (val_to_nat a) (val_to_nat s)); [left; constructor; assumption |].
  right; intro Hfail; apply H0; inversion Hfail; assumption.
Qed.
Lemma List_elements_equal_decidable (l1 l2 : list sval) : DecidableAsn (embed (List_elements_equal l1 l2)).
Proof.
  intros Pr n h; simpl.
  generalize dependent l2.
  induction l1.
  * intro l2; destruct l2.
    - left; intro e; split; intro H; exfalso; eapply in_nil; eassumption.
    - right; intro Hfail.
      specialize (Hfail s); destruct Hfail as [_ Hfail].
      eapply in_nil; apply Hfail; apply in_eq.
  * intro l2; destruct (IHl1 l2).
    + destruct (in_dec dec_eq a l2).
      - left; intro e; split; intro H'; specialize (H e).
          apply in_inv in H'; destruct H'; [ subst; assumption | apply H; assumption].
          apply H in H'; apply in_cons; apply H'.
      - right; intro Hfail; apply n0.
        apply Hfail. constructor; reflexivity.
    + admit.
Qed.  

Lemma Sorted_of_decidable (l1 l2 : list sval) : DecidableAsn (embed (Sorted_of l1 l2)).
Proof.
  pose proof (List_sorted_decidable l2).
  eapply decidable_andI in H; [| apply (List_elements_equal_decidable l1 l2)].
  apply H.
Qed.


Definition sort_spec : pspec := 
  @lforall pspec _ _ (fun (xs : list sval) => 
    "C" :.: "sort" |-> ("l"::nil) {{
      embed (`List_rep "l"/V `xs)
    }}-{{
      "r", embed(@lexists sasn _ _ (fun (ys : list sval) => @lembedand (open Prop) sasn _ _ (`Sorted_of `xs `ys) (`List_rep "r"/V `ys)))
    }}
  ).
Print sort_spec.

Definition merge_spec : pspec :=
  @lforall pspec _ _ (fun (l1 : list sval) => (@lforall pspec _ _ (fun (l2 : list sval) => 
    "C" :.: "merge" |-> ("l1"::"l2"::nil) {{
      embed (@land sasn _ (@lembedand (open Prop) sasn _ _ (`List_sorted `l1) (`List_rep "l1"/V `l1) ) (@lembedand (open Prop) sasn _ _ (`List_sorted `l2) (`List_rep "l2"/V `l2) ) )
    }}-{{
      "l", embed(@lexists sasn _ _ (fun (ys : list sval) => @lembedand (open Prop) sasn _ _ (`Sorted_of `(l1 ++ l2) `ys) (`List_rep "l"/V `ys)))
    }}
  ))).
Print merge_spec.

Definition split_spec : pspec :=
  @lforall pspec _ _ (fun (l : list sval) => 
    "C" :.: "split" |-> ("l"::nil) {{
      embed(`List_rep "l"/V `l)
    }}-{{
      "r", embed (@lexists sasn _ _ (fun r1 => @lexists sasn _ _ (fun l1 => @lexists sasn _ _ (fun r2 => @lexists sasn _ _ (fun l2 =>
         @lembedand (open Prop) sasn _ _ `(l = l1 ++ l2) (@land sasn _ (`pointsto "r"/V `"fst" r1)
           (@land sasn _ (`List_rep r1 `l1) (@land sasn _ (`pointsto "r"/V `"snd" r2) (`List_rep r2 `l2) ))
         ))
      ))))
    }}
  ).
Print split_spec.

Import STNotations.
Definition MS_spec : pspec :=
  @lforall pspec _ _ (fun (xs : list sval) => (@lforall pspec _ _ (fun (ys : list sval) =>
    "C" :.: "MS" |-> ("x"::nil) {{
      has_ST "x" (st_recv "i" (`List_rep "i"/V `xs) 
                 (st_send "o" (@lembedand (open Prop) sasn _ _ (`Sorted_of `ys `ys) (`List_rep "o"/V `ys )) 
                 st_end))
    }}-{{
      "_", all_STs st_end
    }}
  ))).
Print MS_spec.
