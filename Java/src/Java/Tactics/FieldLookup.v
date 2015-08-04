Require Import MirrorCore.RTac.Core.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Lambda.ExprUnify_simul.

Require Import Java.Func.JavaFunc.
Require Import Java.Func.JavaType.
Require Import Java.Language.Program.
(*
Require Import Charge.ModularFunc.BaseFunc.

Section FieldLookup.
  Context {fs : Environment}.

  Definition FIELD_LOOKUP : rtac typ (expr typ func) :=
	fun tus tvs n m c s e =>
		match e with
		  | App (App (App (Inj ({| SumN.index := 1%positive; SumN.value := pFieldLookup |}))
		  	 (Inj (({| SumN.index := 1%positive; SumN.value := pProg P |})))) C) f =>
		    match baseS C with
		      | Some (pString C') =>
				match class_lookup C' P with
		    	  | Some Class =>
		    	    match @exprUnify (ctx_subst c) typ func _ _ _ _ _ 3
		                             tus tvs 0 f (mkFields (c_fields Class)) tyVarList s with
		              | Some s => Solved s
		              | None   => Fail
		            end
				  | _ => Fail
				end
			  | _ => Fail
			end
		  | _ => Fail
		end.

Lemma FIELD_LOOKUP_sound : rtac_sound FIELD_LOOKUP.
Proof.
  unfold rtac_sound, rtac_spec; intros.
  unfold FIELD_LOOKUP, fieldLookupTac in H.
  destruct g; subst; try apply I.
  forward.
  simpl in H10.
  forward.
  SearchAbout exprUnify'.
  Print exprUnify'.
  Print ExprUnify_common.unify_sound_ind.
  pose proof (exprUnify_sound).
  specialize(H13 (ctx_subst ctx) typ func _ _ _ _ _ _ _ _ _ _ 3).
  red in H13.
  red in H13.
  apply H13 with (tv' := nil) in H10; clear H13; [|assumption].
  forward_reason; split; auto.
  forward. simpl in H13.
  simpl in H15.
  unfold Ctx.propD, exprD'_typ0 in H15.
  forward; inv_all; subst.
  simpl in H15.
  autorewrite with exprD_rw in H15; [|apply _];
  simpl in H15; forward; inv_all; subst.
  autorewrite with exprD_rw in H0.
  simpl in H0; forward; inv_all; subst.
  autorewrite with exprD_rw in H2; [|apply _];
  simpl in H2; forward; inv_all; subst.
  autorewrite with exprD_rw in H2; [|apply _];
  simpl in H2; forward; inv_all; subst.
  unfold funcAs in H2. simpl in H2.
  forward; inv_all; subst.
  pose proof (pctxD_substD H12 H14).
  destruct H as [? [? ?]].
  specialize (H13 _ _ _ H5 eq_refl H).
  forward; inv_all; subst.
  destruct H6 as [? [? ?]].
  pose proof (substD_pctxD _ H10 H14 H6).
  destruct H13 as [? [? ?]].
  simpl in *. unfold Expr_expr.
  rewrite H13.
  split. admit.
  intros. unfold exprT_App, exprT_Inj in *; simpl in *.
  destruct e0; inv_all; try congruence.
  destruct f; try congruence.
  destruct s1; try congruence.
  destruct s1; try congruence.
  destruct s1; try congruence.
  destruct s1; try congruence.
  destruct s1; try congruence.
  inv_all; subst. simpl in *.
  Check Ap_pctxD.
  gather_facts.
  eapply Pure_pctxD; eauto.
  intros.
  specialize (H7 _ _ H8).
  destruct H7 as [? ?]. specialize (H15 HList.Hnil). simpl in H15.
  rewrite H15; clear H15.
  unfold field_lookup. exists c; split; [|reflexivity].
  autorewrite with exprD_rw in H3; [|apply _];
  simpl in H2; forward; inv_all; subst.
  simpl.
  unfold eq_rect_r. simpl.
  
  Require Import ExtLib.Data.String.
  
  Lemma class_lookup_sound s p c (H : class_lookup s p = Some c) : In (s, c) (p_classes p).
  Proof.
    destruct p. induction p_classes; simpl in *.
    * unfold class_lookup in H. simpl in H; congruence.
    * unfold class_lookup in H. simpl in H.
      destruct a; simpl in *. consider (s ?[ eq ] s0); intros; subst.
      + left. rewrite rel_dec_eq_true in H; inv_all; subst; [reflexivity| apply _|reflexivity].
      + right. rewrite rel_dec_neq_false in H; [apply IHp_classes; apply H | apply _ | apply H0].
  Qed.
  
  apply class_lookup_sound.
  apply H9.
  apply _.
Qed.

End FieldLookup.

*)