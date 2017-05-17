Require Import Coq.Strings.String.
Require Import Coq.PArith.BinPos.

Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.String.
Require Import ExtLib.Data.Nat.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Structures.Applicative.
Require Import ExtLib.Tactics.

Require Import MirrorCore.PLemma.
Require Import Charge.Tactics.Rtac.Red.
Require Import Charge.Tactics.Rtac.PApply.

Require Import MirrorCore.Lemma.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.RTac.RTac.
Require MirrorCore.syms.SymEnv.
Require MirrorCore.syms.SymSum.
Require Import MirrorCore.Subst.FMapSubst.
Require Import MirrorCore.Lambda.ExprLift.
Require Import MirrorCore.Lambda.ExprSubst.
Require Import MirrorCore.Lambda.ExprUnify_simul.
Require Import MirrorCore.Lambda.ExprTac.
Require Import MirrorCore.Lambda.Red.
Require Import MirrorCore.Lambda.AppN.
Require Import MirrorCore.Lambda.RedAll.
Require Import MirrorCore.Lambda.ExprVariables.
Require Import MirrorCore.Lambda.Rtac.
Require Import MirrorCore.Lambda.Ptrns.
Require Import MirrorCore.Lib.ListOpView.
Require Import MirrorCore.Views.Ptrns.
Require Import MirrorCore.Views.FuncView.
Require Import Charge.Views.ILogicView.
Require Import MirrorCore.Lib.ApplicativeView. 
Require Import Java.Semantics.OperationalSemantics.
Require Import Java.Logic.SpecLogic.
Require Import Java.Logic.AssertionLogic.
Require Import ChargeCore.Logics.ILogic.
Require Import ChargeCore.Logics.BILogic.

Require Import Charge.Views.ILogicView.
Require Import Charge.Patterns.ILogicPattern.
(*
Require Import Charge.Tactics.OrderedCanceller.
Require Import Charge.Tactics.BILNormalize.
Require Import Charge.Tactics.SynSepLog.
Require Import Charge.Tactics.SepLogFold.
*)
Require Import Java.Func.JavaType.
Require Import Java.Func.JavaFunc.
Require Import Java.Tactics.Semantics.

Require Import Charge.Views.SubstView.
Require Import Charge.Views.BILogicView.
Require Import Charge.Patterns.BILogicPattern.
Require Import ChargeCore.Logics.ILogic.
Require Import Charge.Tactics.Rtac.ReifyLemma.
Require Import Charge.Tactics.Rtac.Minify.
(*
Require Import Charge.Tactics.Rtac.PullConjunct.
*)
Require Import MirrorCore.Reify.Reify.

Require Import Java.Func.Reify.
(*
Require Import Charge.Tactics.Open.Subst.
*)

Require Import Java.Language.Lang.
Require Import Java.Language.Program.
Require Import Java.Tactics.Tactics.

Require Import Charge.Tactics.Rtac.Apply.
Require Import Charge.Tactics.Rtac.Cancellation.
Require Import Charge.Tactics.Rtac.Intro.
Require Import Charge.Tactics.Rtac.EApply.
Require Import Charge.Tactics.Rtac.Instantiate.

Require Import Coq.Arith.Peano_dec.
Require Import MirrorCore.CTypes.BaseType.
Require Import MirrorCore.CTypes.ProdType.
Require Import MirrorCore.CTypes.ListType.
Require Import MirrorCore.CTypes.GenericTypes.
Require Import Charge.Rewriter.ILogicRewrite.
Require Import Charge.Rewriter.BIlogicRewrite.
Require Import MirrorCore.Lambda.PolyInst.

Require Import Java.Func.Type.

Fixpoint mkStars n P Q : expr typ func :=
	match n with
		| 0 => mkStar tySasn P Q
		| S n => mkStar tySasn (mkStars n P Q) (mkStars n P Q)
	end.

Definition cancelTest n :=
      mkForall tySasn tyProp
      (mkForall tySasn tyProp
          (mkEntails tySasn (mkStars n (Var 0) (Var 1)) (mkStars n (Var 1) (Var 0)))).


Section blurb.

(*Context {fs : Environment}.*)
Instance fs : Environment := 
  Build_Environment (FMapPositive.PositiveMap.empty (SymEnv.function typ _)).
Time Eval vm_compute in typeof_expr nil nil (cancelTest 10).

Fixpoint search_NoDup
    {A} (A_dec: forall a b: A, {a=b}+{a=b->False}) (l: list A) : option (NoDup l) :=
  match l with
  | nil => Some (NoDup_nil A)
  | a::l' =>
      match search_NoDup A_dec l' with
      | Some nodup =>
          match In_dec A_dec a l' with
          | left isin => None
          | right notin =>
 			match search_NoDup A_dec l' with
 				| Some pf => Some (NoDup_cons _ notin pf)
 				| None => None
            end
          end
      | None => None
      end
  end.

(*


Definition list_notin_set lst s :=
  	fold_right (fun a acc => andb (SS.for_all (fun b => negb (string_dec a b)) s) acc) true lst.

Definition method_specI : stac typ (expr typ func) subst :=
  fun tus tvs s lst e =>
    match e with
    	| mkEntails [l, mkProgEq [mkProg [P]], mkMethodSpec [C, m, mkVarList [args], mkString [r], p, q]] =>
    	      match C, m with
    	        | Inj (inl (inr (pString Cname))), Inj (inl (inr (pString Mname))) =>
    	          match SM.find Cname (p_classes P) with
    	          	| Some Class =>
    	          	  match SM.find Mname (c_methods Class) with
    	          	    | Some Method =>
						  match search_NoDup Coq.Strings.String.string_dec args with
						  	| Some pf =>
						  	  match eq_nat_dec (length args) (length (m_params Method)) with
						  	    | left pf' =>
						  	      if list_notin_set args (modifies (m_body Method)) then
						  	        More tus tvs s lst
						  	        mkEntails [l, mkProgEq [mkProg [P]],
						  	                      mkTriple [mkApplyTruncSubst [tyAsn, p, mkSubstList [mkVarList [args], mkExprList [map E_var (m_params Method)]] ], mkCmd [m_body Method],
						  	                               mkApplyTruncSubst [tyAsn, q, mkSubstList [mkVarList [r::args], mkConsExprList [App fEval (mkExpr [m_ret Method]), mkExprList[map E_var (m_params Method)]]] ]]]
						  	      else
						  	        @Fail _ _ _
						  	    | right _ => @Fail _ _ _
						  	  end
						  	| None => @Fail _ _ _
						  end
    	          	    | None => @Fail _ _ _
    	          	  end
    	          	| None => @Fail _ _ _
    	          end
    	        | _, _ => @Fail _ _ _
    	      end
      	| _ => @Fail _ _ _
    end.
*)
Lemma andA_temp {A : Type} `{IL : ILogic A} (P Q R S : A) (H : lentails (land P (land Q R)) S) : lentails (land (land P Q) R) S.
Proof.
  admit.
Admitted.

Lemma test (P : Prop) (H : P) : P.
Proof.
  intuition.
Qed.

Definition test_lemma : lemma typ (expr typ func) (expr typ func).
Proof.
  reify_lemma reify_java test.
Defined.

Print test_lemma.

Definition andA_temp_lemma : lemma typ (expr typ func) (expr typ func).
reify_lemma reify_java andA_temp.
Defined.
Print andA_temp_lemma.

(** Skip **)
Definition skip_lemma : lemma typ (expr typ func) (expr typ func).
reify_lemma reify_java rule_skip.
Defined.

Lemma skip_lemma_sound :
  @lemmaD typ (expr typ func) RType_typ Expr_expr _ (exprD_typ0 (T:=Prop)) _ nil nil skip_lemma.
Proof.
  unfold lemmaD; simpl; intros.
  unfold AbsAppI.exprT_App, exprT_Inj, Rcast_val, Rcast in * ; simpl in *.
  apply rule_skip. apply H.
Qed.
(*
Example test_skip_lemma : test_lemma skip_lemma. Admitted.
*)
Definition skip_lemma2 : lemma typ (expr typ func) (expr typ func).
reify_lemma reify_java rule_skip2.
Defined.

Print skip_lemma2.
(*
Example test_skip_lemma2 : test_lemma skip_lemma2. Admitted.
*)
Definition seq_lemma (c1 c2 : cmd) : lemma typ (expr typ func) (expr typ func).
Proof.
  reify_lemma reify_java (@rule_seq c1 c2).
Defined.

Lemma seq_lemma_sound c1 c2 :
	lemmaD (exprD_typ0 (T:=Prop)) nil nil (seq_lemma c1 c2).
Proof.
  unfold lemmaD; simpl; intros.
  unfold AbsAppI.exprT_App, exprT_Inj, Rcast_val, Rcast in * ; simpl in *.
  eapply rule_seq; [apply H | apply H0].
Qed.
(*
Example test_seq_lemma (c1 c2 : cmd) : test_lemma (seq_lemma c1 c2). Admitted.
*)
Definition if_lemma (e : dexpr) (c1 c2 : cmd) : lemma typ (expr typ func) (expr typ func).
Proof.
  reify_lemma reify_java (@rule_if e c1 c2).
Defined.

Print if_lemma.

Lemma if_lemma_sound e c1 c2 :
	lemmaD (exprD_typ0 (T:=Prop)) nil nil (if_lemma e c1 c2).
Proof.
  unfold lemmaD; simpl; intros.
  unfold lemmaD'; simpl.
  unfold exprD_typ0; simpl.
  unfold lambda_exprD; simpl.
  admit.
Admitted.
(*
Example test_if_lemma e (c1 c2 : cmd) : test_lemma (if_lemma e c1 c2). Admitted.
*)
Definition read_lemma (x y : String.string) (f : field) : lemma typ (expr typ func) (expr typ func).
Proof.
  reify_lemma reify_java (@rule_read_fwd x y f).
Defined.

Print read_lemma.

Lemma read_lemma_sound x y f : ReifiedLemma (read_lemma x y f).
Proof.
  split.
  unfold lemmaD; simpl; intros.
  unfold read_lemma, lemmaD'; simpl.
  repeat (unfold AbsAppI.exprT_App; simpl in *).
          eapply rule_read_fwd; [eapply H | eapply H0].
Qed.

(*
Example test_read_lemma x y f : test_lemma (read_lemma x y f). Admitted.
*)
Set Printing Width 140.

Definition write_lemma (x : Lang.var) (f : field) (e : dexpr) : lemma typ (expr typ func) (expr typ func).
Proof.
  reify_lemma reify_java (@rule_write_fwd x f e).
Defined.

Print write_lemma.


Lemma write_lemma_sound x f e : ReifiedLemma (write_lemma x f e).
Proof.
  split.
  unfold lemmaD; simpl; intros.
  unfold write_lemma, lemmaD'; simpl; intros.
  unfold exprD_typ0, exprD, Expr_expr, Expr.Expr_expr, lambda_exprD; simpl.
  repeat (unfold AbsAppI.exprT_App; simpl in *).
(*          eapply (rule_write_fwd).*)
  admit.
Admitted.

(*
Example test_write_lemma x f e : test_lemma (write_lemma x f e). Admitted.
*)
Definition assign_lemma (x : Lang.var) (e : dexpr) : lemma typ (expr typ func) (expr typ func).
Proof.
  reify_lemma reify_java (@rule_assign_fwd x e).
Defined.

Print assign_lemma.

Definition assign_lemma_sound x e :
  lemmaD (exprD_typ0 (T := Prop)) nil nil (assign_lemma x e).
Proof.
  unfold lemmaD; simpl; intros.
  unfold lemmaD'; simpl; intros.
  unfold exprD_typ0, exprD, Expr_expr, Expr.Expr_expr, lambda_exprD; simpl.
  repeat (unfold AbsAppI.exprT_App; simpl in *).
  
  admit.
Admitted.

(*
Example test_assign_lemma x e : test_lemma (assign_lemma x e). Admitted.
*)
Definition alloc_lemma (x : Lang.var) (C : class) : lemma typ (expr typ func) (expr typ func).
Proof.
  reify_lemma reify_java (@rule_alloc_fwd x C).
Defined.
(*
Example test_alloc_lemma x C : test_lemma (alloc_lemma x C). Admitted.
*)

Definition alloc_lemma_sound (x : Lang.var) (C : class) :
  lemmaD (exprD_typ0 (T := Prop)) nil nil (alloc_lemma x C).
Proof.
  unfold lemmaD, lemmaD'; simpl in *.
  admit.
Admitted.

Definition pull_exists_lemma : lemma typ (expr typ func) (expr typ func).
Proof.
  reify_lemma reify_java (@pull_exists val).
Defined.
(*
Example test_pull_exists_lemma : test_lemma pull_exists_lemma. Admitted.
*)
Eval vm_compute in pull_exists_lemma.


Definition ent_exists_right_lemma : lemma typ (expr typ func) (expr typ func).
Proof.
  reify_lemma reify_java (@ent_right_exists val).
Defined.

Definition ent_exists_left_lemma : lemma typ (expr typ func) (expr typ func).
Proof.
  reify_lemma reify_java (@ent_left_exists val).
Defined.
(*
Example test_pull_exists_lemma2 : test_lemma ent_exists_right_lemma. Admitted.
*)
Definition eq_to_subst_lemma : lemma typ (expr typ func) (expr typ func).
Proof.
  reify_lemma reify_java eq_to_subst.
Defined.

Print eq_to_subst_lemma.
(*
Eval vm_compute in eq_to_subst_lemma.
*)
(*
Example test_eq_lemma : test_lemma (eq_to_subst_lemma). Admitted.
*)
(*
Definition scall_lemma (x : Lang.var) (C : class) (m : string) (es : list dexpr)
  : lemma typ (expr typ func) (expr typ func).
Proof.
  reify_lemma reify_java rule_static_complete.
Qed.
*)
(*
Example test_pull_exists : test_lemma (pull_exists_lemma). Admitted.
*)
(*

  Lemma foldTacOk : partial_reducer_ok foldTac.
  Proof.
    unfold partial_reducer_ok; intros.
    unfold foldTac.
    remember (listS e); destruct o; [| exists val; tauto].
    destruct l; try (exists val; tauto).
    destruct es; try (exists val; tauto).
    destruct es; try (exists val; tauto).
    destruct es; try (exists val; tauto).
    destruct e2; try (exists val; tauto).
    destruct f; try (exists val; tauto).

    destruct j; try (exists val; tauto).
    destruct es; try (exists val; tauto).
    destruct e; simpl in Heqo; try congruence.
    destruct f; simpl in Heqo; try congruence.
    destruct s; simpl in Heqo; try congruence.
    destruct s; simpl in Heqo; try congruence.
    destruct s; simpl in Heqo; try congruence.
    destruct s; simpl in Heqo; try congruence.
    inv_all; subst.
    autorewrite with exprD_rw in H; simpl in H; forward; inv_all; subst.
    autorewrite with exprD_rw in H; simpl in H; forward; inv_all; subst; [|apply _].
    autorewrite with exprD_rw in H; simpl in H; forward; inv_all; subst; [|apply _].
    autorewrite with exprD_rw in H0; simpl in H0; forward; inv_all; subst; [|apply _].
    autorewrite with exprD_rw in H2; simpl in H2; forward; inv_all; subst; [|apply _].
    unfold funcAs in H2.
    Opaque type_cast.
    simpl in H2. forward; inv_all; subst. red in r. inv_all.
    inversion r; subst.
    rewrite (UIP_refl r) in H4. unfold Rcast in H4; simpl in H4.
    inversion H4; unfold eq_rect_r in H6; simpl in H6.
    subst. clear H4.
    clear H2 r.
    Opaque beta.
    simpl.
    unfold exprT_App, eq_rect_r. simpl.
    cut (exists val' : exprT tus tvs (typD t),
  ExprDsimul.ExprDenote.exprD' tus tvs t
    (fold_right
       (fun (x : string) (acc : expr typ func) =>
        beta (beta (App (App e0 (mkString x)) acc))) e1 l) = Some val' /\
  (forall (us : hlist typD tus) (vs : hlist typD tvs),
   fold_right (e4 us vs) (e3 us vs) (exprT_Inj tus tvs l us vs) = val' us vs)).
   intros [? [? ?]].
   eexists; split; [eassumption | intros; apply H4].
    induction l; simpl; intros.

    + exists e3; tauto.
    + destruct IHl as [? [? ?]].
      eexists; split; [|intros; reflexivity].

  Lemma exprD'_remove_beta tus tvs t e de (H : exprD' tus tvs e t = Some de) :
    exprD' tus tvs (beta e) t = Some de.
  Proof.
    pose proof (beta_sound tus tvs e t).
    unfold exprD' in *. simpl in *. forward; inv_all; subst.
	Require Import FunctionalExtensionality.
	f_equal. symmetry.
    apply functional_extensionality; intros.
    apply functional_extensionality; intros.
    apply H2.
  Qed.


      do 2 (apply exprD'_remove_beta).
      unfold exprD'. simpl.

      red_exprD; [|apply _].
      pose proof (exprD_typeof_Some).
      specialize (H5  _ _ _ _ _ _ _ _ _ _ _ _ _ H2). rewrite H5; clear H5.
      red_exprD; [|apply _].
      forward; inv_all; subst.
      unfold mkString. forward.
      red_exprD; [|apply _].
      Transparent type_cast.
      unfold funcAs. simpl.
	  f_equal. unfold exprT_App; simpl.
	  unfold eq_rect_r. simpl.
	  apply functional_extensionality; intros.
	  apply functional_extensionality; intros.
	  rewrite H4. reflexivity.
Qed.
SearchAbout partial_reducer_ok.

Print partial_reducer_ok.
Print apps_reducer.
Print full_reducer_ok.
Print full_reducer.
Check @idred.
SearchAbout idred.
Print idred.
Print idred'.
Check @beta_all.

Definition FOLD := SIMPLIFY (typ := typ) (fun _ _ _ _ => (beta_all (fun _ => foldTac))).

Require Import ExtLib.Tactics.Consider.
Require Import ExtLib.Tactics.
Require Import MirrorCore.Lambda.RedAll.
Print partial_reducer.

(*
  Lemma foldTacOk2 : partial_reducer_ok foldTac.
  Proof.
    unfold full_reducer_ok; intros.
    Print var_termsP.
    Print partial_reducer_ok.
    unfold exprT, OpenT in P.
    unfold foldTac.
    remember (listS e). destruct o.
    Focus 2.
    simpl.
  Qed.
*)
Lemma FOLD_sound : rtac_sound FOLD.
Proof.
  admit.
  (*
  unfold FOLD.
  apply SIMPLIFY_sound.
  intros; simpl.
  forward.
  rewrite <- H.
  simpl.
  unfold Ctx.propD, exprD'_typ0 in H3; forward; inv_all; subst.
  destruct (beta_all_sound foldTacOk _ _ e0 H3) as [v [H4 H5]].
  apply beta_all_sound.
  Check beta_all_sound.
  (* beta_all_sound is missing *)

  *)
Qed.
*)
Locate rw_fail.
Check SIMPLIFY.
Check SIMPL.

Definition BETA := SIMPL true (red_beta (fun _ => @apps typ func)).

Lemma BETA_sound : rtac_sound BETA.
Proof.
  unfold BETA.
  apply SIMPLIFY_sound.
  intros; simpl; forward.
  (*
  SearchAbout full_reducer.
  assert (full_reducer_ok (fun _ => apps (sym := func))). {
    clear.
    intros e vars tus tvs tus' tvs' P Hvars es t targs Hexpr.
  }
  unfold full_reducer_ok.

  Print full_reducer.
  pose proof (beta_all_sound).
  SearchAbout beta_all.
  rewrite <- H.*)
  admit.
Admitted.

Definition THEN' := @MirrorCore.RTac.Then.THEN typ (expr typ func).

Let EAPPLY lem := THEN' (EAPPLY typ func lem) (MINIFY typ func).

Definition THEN (r1 r2 : rtac typ (expr typ func)) :=
  THEN (THEN (THEN (INSTANTIATE typ func) (runOnGoals r1)) (runOnGoals (INSTANTIATE typ func))) (runOnGoals r2).
Check @red_subst.
Definition substTac (_ : list (option (expr typ func))) (e : expr typ func) (args : list (expr typ func)) := red_subst (apps e args).
Definition SUBST := SIMPL true (red_beta substTac).

Definition EQSUBST := THEN (THEN (TRY (EAPPLY andA_temp_lemma)) (EAPPLY eq_to_subst_lemma)) SUBST.

(*
Notation "'ap_eq' '[' x ',' y ']'" :=
	 (ap (T := Fun stack) (ap (T := Fun stack) (pure (T := Fun stack) (@eq val)) x) y).
*)

(*
Definition match_ap_eq (e : expr typ func) : bool :=
	match e with
	  | App emb (App (App f (App (App g (App h e)) x)) y) =>
	  	match embedS emb, open_funcS f, open_funcS g, open_funcS h, baseS e with
	  		| Some (eilf_embed _ _), Some (of_ap _ _), Some (of_ap _ _), Some (of_const _), Some (pEq _) => true
	  		| _, _, _, _, _ => false
	  	end
	  | _ => false
	end.
*)
(*
Definition PULLEQL : rtac typ (expr typ func) := @PULLCONJUNCTL typ func RType_typ _ _ _ match_ap_eq _ _ _ ilops.
*)
                        (*
	THEN (INSTANTIATE typ func subst) (runOnGoals (THEN (THEN (TRY FIELD_LOOKUP)
		(runOnGoals (CANCELLATION typ func subst tySpec (fun _ => false)))) (runOnGoals FOLD))) ::
		solve_entailment :: nil).
	           *)
(*
Require Import Charge.SetoidRewrite.AutoSetoidRewrite.
Require Import Charge.SetoidRewrite.Base.
Require Import Charge.SetoidRewrite.ILSetoidRewrite.
Require Import Charge.SetoidRewrite.BILSetoidRewrite.
*)
(*
  Definition spec_respects (e : expr typ func) (_ : list (RG (expr typ func)))
	   (rg : RG (expr typ func)) : m (expr typ func) :=
	   match e with
	     | Inj ({|SumN.value:=1%positive; SumN.value := pTriple|}) =>
	       rg_bind (unifyRG (@rel_dec (expr typ func) _ _) rg
	         (RGrespects (RGflip (RGinj (fEntails tySasn)))
	           (RGrespects (RGinj (fEq tyCmd))
	             (RGrespects (RGinj (fEntails tySasn))
	               (RGinj (fEntails tySpec))))))
	         (fun _ => rg_ret fTriple)
	     | _ => rg_fail
	   end.

Definition step_unfold vars rw :=
  setoid_rewrite vars _ (fEntails : typ -> expr typ func) rw
    (sr_combine il_respects
               (sr_combine (@il_respects_reflexive typ func _ _ _ ilops _ _)
                                        (sr_combine bil_respects
                                                    (sr_combine eq_respects
                                                    (sr_combine spec_respects refl)))))
    (fun _ => rw_fail).

  Definition STEP_REWRITE rw : rtac typ (expr typ func) :=
    fun tus tvs lus lvs c s e =>
      match step_unfold (getVars c) rw tyProp e with
        | Some (e', _) => More s (GGoal e')
        | _ => More s (GGoal e)
      end.
*)


Definition PULL_EXISTS : rtac typ (expr typ func) :=
  THEN (THEN (EAPPLY ent_exists_left_lemma) (INTRO typ func)) BETA.

Definition PULL_TRIPLE_EXISTS : rtac typ (expr typ func) :=
  THEN (THEN (EAPPLY pull_exists_lemma) (INTRO typ func)) BETA.
Check @CANCELLATION.

Definition CANCELLATION := CANCELLATION typ func tySasn is_pure.

Definition solve_entailment : rtac typ (expr typ func) :=
  THEN' (THEN (INSTANTIATE typ func)
              (FIRST (SOLVE CANCELLATION ::
                     THEN (REPEAT 1000 EQSUBST) CANCELLATION :: nil))) (MINIFY typ func).

(*
Definition solve_entailment (rw : rewriter (typ := typ) (func := func)) : rtac typ (expr typ func) :=
	THEN (INSTANTIATE typ func)
		(FIRST (SOLVE (CANCELLATION typ func tySasn is_pure) ::
	           (THEN (THEN (THEN (THEN (*PULLEQL*) IDTAC (REPEAT 1000 EQSUBST))
	          (STEP_REWRITE rw)) (REPEAT 1000 (INTRO typ func)))
	              (CANCELLATION typ func tySasn is_pure)::
	           nil))).
*)


(*
Require Import Java.Tactics.FieldLookup.
Require Import Charge.Tactics.Open.Subst.
Require Import Charge.Tactics.Lists.Fold.
*)

(*
Definition FOLD := SIMPL true (red_beta (fun x e args => red_fold (apps e args))).
*)
(*
Definition solve_alloc rw : rtac typ (expr typ func) :=
    THEN (INSTANTIATE typ func)
    (FIRST (SOLVE (CANCELLATION typ func tySpec (fun _ => false)) ::
                        FIELD_LOOKUP ::
                        THEN FOLD (solve_entailment rw) :: nil)).
*)
(*
Definition simStep (rw : rewriter (typ := typ) (func := func)) (r : rtac typ (expr typ func)) :=
    THEN (THEN (THEN (THEN (SUBST typ func (ilp := ilp) (bilp := bilp) (eilp := eilp))
    	(TRY PULL_TRIPLE_EXISTS)) (STEP_REWRITE rw))) (REPEAT 10 PULL_TRIPLE_EXISTS)) r.
*)

Definition simStep (r : rtac typ (expr typ func)) :=
  THEN (INSTANTIATE typ func) (THEN (THEN (THEN (TRY PULL_TRIPLE_EXISTS) SUBST) (TRY EQSUBST)) r).
Print write_lemma.

(*
Set Printing Universes.
Require Import MirrorCore.Views.ListOpView.
Print Universes.
Check @red_fold_ptrn typ func.

Require Import 
*)
(*
Require Import MirrorCore.Views.Ptrns.
Require Import MirrorCore.Views.FuncView.
Require Import MirrorCore.Views.StringView.
Require Import MirrorCore.Lambda.Ptrns.
Check fptrnFieldLookup.
Check fptrnProg.
Print fptrnProg.
Check @ptrn_view.
  Definition FIELD_LOOKUP : rtac typ (expr typ func) :=
    fun tus tvs n m c s =>
      run_ptrn 
        (pmap (fun P_C_f => 
                 let '(_, P, C, f) := P_C_f in
                 match class_lookup C P with
                 | Some C' =>
		   match @exprUnify (ctx_subst c) typ func _ _ _ _ _ 3
		                    tus tvs 0 f (Inj (fFields (c_fields C'))) tyVarList s with
		   | Some s => Solved s
		   | None   => Fail
		   end
                     
                 | None => Fail
                 end)
              (app (app (app (inj (ptrn_view _ fptrnFieldLookup)) 
                             (inj (ptrn_view _ (fptrnProg get))))
                        (ptrnString get))
                   get)) Fail.

Require Import MirrorCore.Views.ListView.

Definition fields_to_list (e : expr typ func) : expr typ func :=
  run_ptrn (inj (pmap 
                      (fun lst => 
                      fold_right (fun x xs => mkCons tyString (mkString x) xs) (mkNil tyString) lst)
                      (ptrn_view _ (fptrnFields get)))) e e.
Definition FIELDS_TO_LIST := 
  SIMPLIFY (typ := typ) (fun _ _ _ _ => beta_all (fun x e args => fields_to_list (apps e args))).
*)
Fixpoint tripleE (c : cmd) : rtac typ (expr typ func) :=
	match c with
(*	    | cskip => simStep rw (THEN (EAPPLY skip_lemma) (solve_entailment rw))
	(*    | calloc x C => simStep rw (THEN (EAPPLY (alloc_lemma x C))
	        (FIRST (solve_alloc rw::solve_entailment rw::nil)))*)
		| cseq c1 c2 => simStep rw (THEN' (EAPPLY (seq_lemma c1 c2))
		    (THENK (runOnGoals (TRY (tripleE c1 rw))) (THENK (MINIFY typ func) (runOnGoals (tripleE c2 rw)))))
		| cassign x e => simStep rw (THEN (EAPPLY (assign_lemma x e)) (solve_entailment rw))
		| cread x y f => simStep rw (THEN (EAPPLY (read_lemma x y f)) (solve_entailment rw))
		| cif e c1 c2 => simStep rw (THEN (EAPPLY (if_lemma e c1 c2)) (solve_entailment rw))
		| cwrite x f e => simStep rw (THEN (EAPPLY (write_lemma x f e)) (solve_entailment rw))*)
                | cskip => THEN (EAPPLY skip_lemma) solve_entailment
		| cread x y f => THEN (EAPPLY (read_lemma x y f)) solve_entailment
(*                | calloc x C => (*THEN' (EAPPLY (alloc_lemma x C))
                                      (ON_EACH (solve_entailment ::
                                                FIELD_LOOKUP ::
                                                THEN FOLD solve_entailment :: nil))*)
                  THEN' (EAPPLY (alloc_lemma x C)) 
                        (ON_EACH (CANCELLATION typ func tySpec (fun _ => false)
                                 ::THEN (INSTANTIATE typ func) FIELD_LOOKUP::
                                 THEN (THEN FIELDS_TO_LIST FOLD) SUBST::nil))*)
                  (*      (ON_EACH (solve_entailment :: IDTAC :: IDTAC :: nil))*)
                | cwrite x f e => THEN (EAPPLY (write_lemma x f e)) solve_entailment
(*		| cseq c1 c2 => THEN' (EAPPLY (seq_lemma c1 c2))
                                      (ON_EACH (tripleE c1::TRY (tripleE c2)::nil))*)
                | cseq c1 c2 => 
                  THEN' (EAPPLY (seq_lemma c1 c2))
                        (ON_EACH 
                           (tripleE c1::
                                    simStep (TRY (tripleE c2))::nil))
		| _ => IDTAC
	end.

Definition ptrnCmd {T : Type}
           (p : ptrn cmd T) : ptrn (expr typ func) T :=
  inj (ptrn_view _ (fptrnCmd p)).

Check rtac typ (expr typ func).
Print rtac.
Definition symE : rtac typ (expr typ func) :=
  fun c cs e =>
    run_ptrn
      (pmap (fun t_l_r => let '(_, _, (_, _, c)) := t_l_r in tripleE c)
            (ptrnEntails ptrn_tySpec ignore (ptrnTriple ignore ignore (ptrnCmd get))))
      FAIL e c cs e.

Definition runTac :=
   (THEN' (THEN (THEN (REPEAT 1000 (INTRO typ func)) symE)
	(INSTANTIATE typ func)) (MINIFY typ func)).

Lemma runTac_sound : rtac_sound runTac.
Proof.
  admit.
Admitted.

Lemma CANCELLATION_sound : rtac_sound CANCELLATION.
Proof.
  admit.
Admitted.

(*
Definition mkPointsto (x : expr typ func) (f : field) (e : expr typ func) : expr typ func :=
   mkAp (func := func) tyVal tyAsn
        (mkAp tyString (tyArr tyVal tyAsn)
              (mkAp tyVal (tyArr tyString (tyArr tyVal tyAsn))
                    (mkPure (tyArr tyVal (tyArr tyString (tyArr tyVal tyAsn)))
                             (Inj fPointsto))
                    x)
              (mkPure (func := func) tyString (mkString f)))
        e  .
*)

Fixpoint seq_skip n :=
	match n with
	  | 0 => cskip
	  | S n => cseq cskip (seq_skip n)
	end.
(*
Local Instance Applicative_Fun A : Applicative (RFun A) :=
{ pure := fun _ x _ => x
; ap := fun _ _ f x y => (f y) (x y)
}.
*)
Definition testSkip n : Prop :=
  forall (G : spec) (P : sasn), G |-- triple P P (seq_skip n).

Lemma INTRO_sound : rtac_sound (INTRO typ func).
Proof.
  admit.
Admitted.
(*
Require Import Java.Tactics.Tactics.
*)
Check runOnGoals.
Definition run_tac tac goal :=
  runOnGoals tac (CTop nil nil)
    (ctx_empty (typ := typ) (expr := expr typ func)) goal.

Ltac run_rtac reify term_table tac_sound :=
  lazymatch type of tac_sound with
    | rtac_sound ?tac =>
	  let name := fresh "e" in
	  lazymatch goal with
	    | |- ?P =>
	      reify_aux reify term_table P name;
	      let t := eval vm_compute in (typeof_expr nil nil name) in
	      let goal := eval unfold name in name in
	      match t with
	        | Some ?t =>
	          let goal_result := constr:(run_tac tac (GGoal name)) in 
	          let result := eval vm_compute in goal_result in
                                                    pose goal_result;
	           lazymatch result with
	            | More_ ?s ?g => 
	              cut (goalD_Prop nil nil g) ; [
	                  change (goalD_Prop nil nil g -> exprD_Prop nil nil name);
                        let H := constr:(@eq_refl (Result (CTop nil nil)) (More_ s g)) in
                        refine(@run_rtac_More  _ tac s _ _ tac_sound _);
                          vm_cast_no_check H
	                | pose (run_tac tac (GGoal name)); cbv_denote
	              ] 
	            | Solved ?s =>
                      let H := constr:(@eq_refl (Result (CTop nil nil)) (Solved s)) in
                      refine (@run_rtac_Solved _ tac s name tac_sound _);
                        vm_cast_no_check H
	            | Fail => idtac "Tactic" tac "failed."
	            | ?x => idtac "Error: run_rtac could not resolve the result from the tactic :" tac; idtac x
	          end 
	        | None => idtac "expression " goal "is ill typed" t
	      end 
	  end
	| _ => idtac tac_sound "is not a soudness theorem."
  end.

          Ltac reify_goal :=
	    lazymatch goal with
	  | |- ?P =>
            let name := fresh "e" in
	    reify_aux reify_java term_table P name
          end.

Open Scope string.
(*
Ltac cbv_denote_typeof_sym :=
  match goal with
  | |- context [typeof_sym ?a] =>
    let r := cbv_denote_tac (typeof_sym a) in 
    idtac a r;
      progress change (typeof_sym a) with r; cbv beta iota delta [blurg]
  end.

Ltac cbv_denote_symD :=
  match goal with
  | |- context [SymI.symD ?a] =>
    let r := cbv_denote_tac (SymI.symD a) in 
    idtac a r;
      progress change (SymI.symD a) with r; cbv beta iota delta [blurg]
  end.
*)
 
 
Lemma test_read : ltrue |--
    triple 

      ((ap_pointsto [("o" : string), ("f" : field), pure (T := RFun (string -> val)) (vint 3)])  **
       ap_pointsto [("o" : string), ("g" : field), pure (T := RFun (string -> val)) (vint 4)])
      (ap_pointsto [("o" : string), ("f": field), pure (T := RFun (string -> val)) (vint 3)] **
      (ap_pointsto [("o" : string), ("g": field), pure (T := RFun (string -> val)) (vint 4)]))
      (cseq (cread "x" "o" "f") (cseq (cread "y" "o" "g") cskip)).
Proof.
  Time run_rtac reify_java term_table runTac_sound.
Time Qed.

Definition myTac :=
  THEN (REPEAT 2 (INTRO typ func)) solve_entailment.

Definition substTac2 :=
  THEN (REPEAT 10 (INTRO typ func)) SUBST.

Lemma substTac2_sound : rtac_sound substTac2.
Proof.
  admit.
Admitted.

Ltac solve_subst :=
  run_rtac reify_java term_table substTac2_sound.

(*
Require Import Java.Examples.ListClass.
*)
Ltac charge := run_rtac reify_java term_table runTac_sound; intros.
(*
Require Import MirrorCore.syms.SymOneOf.
(*
Lemma FOLD_sound : rtac_sound FOLD.
Proof.
  admit.
Admitted.
*)

(*
Lemma test_alloc : prog_eq ListProg |-- triple ltrue lfalse (calloc "x" "NodeC").
Proof.
  charge.
  
run_rtac reify_java term_table FOLD_sound.
Check 
Print FOLD.
Print alloc_lemma.
Check @ent_left_exists.

Print ent_exists_left_lemma.
reify_goal.
Check @pull_exists.
apply @pull_exists.
Print FOLD.
Print mkString.
Print ptrnString.
eexists.
eexists.
assert (exists x, prog_eq ListProg |-- prog_eq x).

Definition myTac2 : rtac typ (expr typ func) := THEN (INTRO typ func) 
                                                     (CANCELLATION typ func tySpec (fun _ => true)).
                                                                   
                                                                      
Lemma myTac2_sound : rtac_sound myTac2.
Proof.
  admit.
Admitted


run_rtac reify_java term_table myTac2_sound.

reflexivity.
  cbv_denote.
  unfold ListProg. simpl.
  unfold NodeC.
  charge.
*)

Lemma myTac_sound : rtac_sound myTac.
Proof.
  admit.
Admitted.

Lemma solve_entailment_test : forall x, exists y : sasn, x |-- y.
Proof.
  run_rtac reify_java term_table myTac_sound.
Qed.

Lemma test_skip_lemma3 : testSkip 10.
Proof.
  unfold testSkip; simpl.
  Time run_rtac reify_java term_table runTac_sound.
Time Qed.

Print read_lemma.
Print EAPPLY.
Definition test2 a b c := EAPPLY (read_lemma a b c).

Lemma test_sound a b c : rtac_sound (test2 a b c).
Proof.
  admit.
Admitted.

Require Import MirrorCore.AbsAppI.

Lemma test_write :
	ltrue |--
	triple
      (ap_pointsto [("o": String.string), ("f" : field), pure (T := RFun (string -> val)) (vint 3)])
      (ap_pointsto [("o": String.string), ("f": field), pure (T := RFun (string -> val)) (vint 4)])
      (cseq (cwrite "o" "f" (E_val (vint 4))) cskip).
Proof.
  Time run_rtac reify_java term_table runTac_sound.
Time Qed.

Definition a : field := "a".
Definition b : field := "b".

Definition Test_swap2_body := (cseq (cseq (cread ("x")%string ("this")%string a) (cseq (cread ("y")%string ("this")%string b) (cseq (cwrite ("this")%string a (E_var ("y")%string)) (cwrite ("this")%string b (E_var ("x")%string))))) cskip).
Definition Test_swap2_Method := (Build_Method (("this")%string :: nil) Test_swap2_body (E_val nothing)).
Definition Test_Class := (Build_Class (a :: b :: nil)) ((("swap2")%string, Test_swap2_Method) :: nil).
Theorem Test_swap2_s : lentails ltrue (triple
  (
    ap_pointsto [("this")%string, a, eval (E_val ((0)%Z))] **
    ap_pointsto [("this")%string, b, eval (E_val ((1)%Z))] ** empSP
  )
  (
    ap_pointsto [("this")%string, a, eval (E_val ((1)%Z))] **
    ap_pointsto [("this")%string, b, eval (E_val ((0)%Z))] ** empSP
  )
  Test_swap2_body
).
Proof.
  unfold Test_swap2_body.
  Time charge.
Qed.




Definition Test_swap2_body2 := (cseq (cread "x" "this" a) (cseq (cread "y" "this" b) (cseq (cwrite "this" a (E_var "y")) (cseq (cwrite "this" b (E_var "x")) cskip)))).
Theorem Test_swap3_s : lentails ltrue (triple
  (
    ap_pointsto ["this", a, eval (E_val 0%Z)] **
    ap_pointsto ["this", b, eval (E_val 1%Z)] ** empSP
  )
  (
    ap_pointsto ["this", a, eval (E_val 1%Z)] **
    ap_pointsto ["this", b, eval (E_val 0%Z)] ** empSP
  )
Test_swap2_body2
).
Proof.
  unfold Test_swap2_body2.
  Time charge.
Time Qed.

Lemma test3 :
 
lentails ltrue (triple
   ( ap_pointsto ["o", a, eval (E_val 1%Z)] **
       ap_pointsto ["o", b, eval (E_val 0%Z)] ** empSP)
    (ap_pointsto ["o", a, eval (E_val 0%Z)] **
      ap_pointsto ["o", b, eval (E_val 1%Z)] ** empSP )

    (cseq (cread "x1" "o" a)
    (cseq (cread "x0" "o" b)
    (cseq (cwrite "o" a (E_var "x0"))
    (cseq (cwrite "o" b (E_var "x1")) cskip))))).
Proof.
  charge.
Qed.
*)

Definition PULL_EXISTS2 : rtac typ (expr typ func) :=
  REWRITE (ilops := ilops) 
          func_unify 
          (List.app (ILogicRewrite.pull_exists_lemmasL (ilops := ilops)) (BIlogicRewrite.pull_exists_lemmasL (bilops := bilops))) 
          (bil_proper (bilops := bilops)).

Definition rewrite_it := 
  THEN (REPEAT 3 (INTRO typ func)) 
       (THEN (INSTANTIATE typ func)
             (RED_ENTAILS expr_typ)).

Theorem rewrite_it_sound : rtac_sound rewrite_it.
  admit.
Admitted.
Definition REFL :=
  THEN (REPEAT 4 (INTRO typ func)) (THEN (TRY (INSTANTIATE typ func)) 
                                         (PAPPLY func_unify (plem_entails_refl (ilops := ilops)))).

Theorem REFL_sound : rtac_sound REFL.
Proof.
  admit.
Admitted.

Transparent ILInsts.ILFun_Ops.


(*

Lemma test2 : forall (P : nat -> RFun (string -> val) asn) (Q : RFun (string -> val) asn), True.
intros.
assert ((ltrue : sasn) //\\ Q //\\ (Exists n : nat, P n) |-- ltrue).
Transparent ILInsts.ILFun_Ops.
intro s.
generalize dependent s. generalize dependent Q. generalize dependent P.
unfold Lang.var.
run_rtac reify_java term_table rewrite_it_sound.
run_rtac reify_java term_table REFL_sound.
clear r0.
Locate expr_typ.
Print expr_typ.
vm_compute in r2.
unfold rewrite_it in r.
vm_compute in r.
match goal with
| H := More_ _ ?g |- _ => 
   assert (goalD_Prop nil nil g)
end.
Print goalD.

Eval simpl in (typD (@CoreTypes.tyArr typ'
                 (@CoreTypes.tyBase0 typ'
                    (TSymOneOf.OneOfType.mkOneOfF typ_map O (xI xH) tString))
                 (@CoreTypes.tyBase0 typ'
                    (TSymOneOf.OneOfType.mkOneOfF typ_map O (xO (xO xH)) tVal)))).
Locate RED_ENTAILS.
Check typD.
Print Quant._foralls.
unfold goalD_Prop.
Opaque goalD. simpl.
Transparent goalD.
unfold goalD.
Eval vm_compute in tyVal.
Eval vm_compute in (typ0 (F := val)).
unfold propD.
unfold exprD_typ0.
unfold exprD.
unfold Expr_expr.
unfold Expr.Expr_expr.
unfold lambda_exprD.
cbv_denote_func_simul.
unfold typ2_match.
unfold Typ2_tyArr.
unfold CoreTypes.Typ2_Fun.
unfold exprT_GetVAs.
SearchAbout Goal.
match goal with
| |- context [nth_error_get_hlist_nth typD ?l] =>
  let t := eval vm_compute in (nth_error_get_hlist_nth typD l) in idtac t
end.
unfold nth_error_get_hlist_nth.
match goal with 
| |- context [func_simul ?a] => 
  let t := eval simpl in (func_simul a) in pose t
end.
idtac.
Print rtac.

assert (INTRO typ func (CTop nil nil) (TopSubst (expr typ func) nil nil) (mkForall (typ2 (typ0 (F:=string)) (typ0 (F:=val))) (typ0 (F:=Prop))
         (App
            (App (Inj (fEntails tyAsn))
               (App
                  (App
                     (App (Inj (fAnd (typ2 (typ2 (typ0 (F:=string)) tyVal) tyAsn)))
                        (mkTrue (typ2 (typ2 (typ0 (F:=string)) tyVal) tyAsn)))
                     (mkTrue (typ2 (typ2 (typ0 (F:=string)) tyVal) tyAsn))) 
                  (ExprCore.Var 3)))
            (App (mkTrue (typ2 (typ2 (typ0 (F:=string)) tyVal) tyAsn)) (ExprCore.Var 2)))) = Fail).
vm_compute.
unfold rewrite_it.
unfold mkForall.
Opaque RED_ENTAILS.
simpl.
unfold THEN.
simpl.
unfold INSTANTIATE.
simpl.
unfold RTac.Instantiate.INSTANTIATE.
simpl.
unfold SIMPLIFY; simpl.
unfold RTac.Then.THEN.
simpl.
Print beta.
Print substitute_one.
Transparent RED_ENTAILS.
unfold RED_ENTAILS.
unfold run_ptrn.
unfold pmap.
unfold red_entails_lhs.
unfold pmap.
unfold ptrnEntails.

unfold app.
unfold Mbind, Mrebuild.
Print mkEntails.
unfold ptrn_view.
unfold get.
Print mkForall.
Check ptrn_view.
unfold inj.
unfold THEN, REPEAT, INSTANTIATE.
unfold RTac.Instantiate.INSTANTIATE.
unfold SIMPLIFY. unfold REPEAT'.

vm_compute in r0.

unfold tyVal in e. simpl in e.
Check @run_ptrn.
Check red_entails_lhs.

Eval vm_compute in
  (run_ptrn
    (red_entails_lhs expr_typ)
    (ExprCore.Var 0)
    (App
       (App (Inj (fEntails tyAsn))
            (App
               (App
                  (App (Inj (fAnd (typ2 (F := Fun) (typ2 (F := Fun) (typ0 (F:=string)) tyVal) tyAsn)))
                       (mkTrue (typ2 (F := Fun) (typ2 (F := Fun) (typ0 (F:=string)) tyVal) tyAsn)))
                  (mkTrue (typ2 (F := Fun) (typ2 (F := Fun) (typ0 (F:=string)) tyVal) tyAsn))) 
               (ExprCore.Var 0)))
       (App (mkTrue (typ2 (F := Fun) (typ2 (F := Fun) (typ0 (F:=string)) tyVal) tyAsn)) (ExprCore.Var 0)))).

Eval vm_compute in
    (run_ptrn
       (il_pointwise_red (fun _ e => e) expr_typ)
       (ExprCore.Var 0)
       ((App
                     (App (Inj (fAnd (typ2 (F := Fun) (typ2 (F := Fun) (typ0 (F:=string)) tyVal) tyAsn)))
                        (mkTrue (typ2 (F := Fun) (typ2 (F := Fun) (typ0 (F:=string)) tyVal) tyAsn)))
                     (mkTrue (typ2 (typ2 (typ0 (F:=string)) tyVal) tyAsn))))).
       (ExprCore.Var 0)).
Print run_ptrn.
Print inj.
Eval vm_compute in 
    (expr_typ 

Set Printing Implicit.
Check @red_entails_lhs.

replace stack with (String.string -> val) by reflexivity.

reify_java ((Q //\\ Q) t).

run_rtac reify_java term_table (RED_ENTAILS_sound expr_typ).

simpl.

assert (ap (T := RFun stack) (@pure (RFun stack) (Applicative_RFun stack) (forall U : Type, (U -> asn) -> asn) (@lexists asn _)) P |-- Q).
assert (lexists (fun x => P x //\\ Q) |-- Q).
intro t.
simpl.
unfold lentails. simpl.
simpl.
unfold ILInsts.ILFun_Ops.
intros a.
Check @lexists.
Check @lexists asn _.
assert (ap (ap (pure land) (ap (T := RFun stack) (pure (T := RFun stack) (@lexists asn _)) P)) Q s |-- (P //\\ Q) s).
assert (ap (ap (pure land) P) Q s |-- (P //\\ Q) s)
simpl.
apply f_equal.
intro s.
reflexivity.
Lemma test_pq : forall (P : nat -> asn) (R : asn),
   ((Exists x, P x) //\\ (Exists x : nat, ((Exists x, P 5 //\\ P x) ** P x))) |-- R.

Ltac rtac_debug :=
  match goal with 
  | H := context [
             match ?a with
             | Fail => _
             | More_ _ _ => _
             | Solved _ => _
             end
           ] |- _ => 
         let r := eval vm_compute in a in
                                      change a with r in H; cbv iota beta in H
  end.


Proof.
  run_rtac reify_java term_table rewrite_it_sound.

Eval compute in (bilops (tyArr (tyArr tyString tyVal) tyAsn)).
  unfold e in r.
  unfold rewrite_it in r.
  simpl in r.
  unfold run_tac in r.
  unfold runOnGoals in r.
  simpl in r.
  unfold THEN in r.
  simpl in r.
  unfold INSTANTIATE in r.
  simpl in r.
  unfold RTac.Instantiate.INSTANTIATE in r.
  simpl in r.
  unfold SIMPLIFY in r. simpl in r. 
  unfold MirrorCore.RTac.Then.THEN in r.
  unfold runOnGoals in r.
  unfold INTRO in r.
  unfold RTac.Intro.INTRO in r.
    
  match goal with 
  | H := context [_subst ?a ?b ?c ?d] |- _ =>
         let r := eval vm_compute in (_subst a b c d) in
                                      change (_subst a b c d) with r in H; cbv beta iota in H
                                          
  end.
  repeat (
  match goal with
  | H := context [fintro ?a] |- _ => 
         let r := eval vm_compute in (fintro a) in 
         change (fintro a) with r in H; cbv beta iota in H
  end).
  unfold More in r.
  unfold TRY in r.
    match goal with 
  | H := context [_subst ?a ?b ?c ?d] |- _ =>
         let r := eval vm_compute in (_subst a b c d) in
                                      change (_subst a b c d) with r in H; cbv beta iota in H
                                          
   end.
    unfold fromAll in r.
    unfold ILogicRewrite.rewrite_it in r.
    unfold Tactic.auto_setoid_rewrite_bu in r.
    unfold BottomUp.bottom_up in r.
    unfold BottomUp.setoid_rewrite in r.
    unfold BottomUp.setoid_rewrite' in r.
    unfold Core.rw_orelse in r.
    unfold Core.rw_bind_catch in r.
    match goal with
    | H := context [@get_respectful ?a ?b ?c ?d ?e ?f ?g ?h ?i ?j ?k ?l ?m] |- _ =>
           let r := eval vm_compute in (@get_respectful a b c d e f g h i j k l m) in
                                        change (@get_respectful a b c d e f g h i j k l m) with r in H; cbv beta iota in H
    end.
    unfold Core.rw_bind in r.
    unfold BottomUp.recursive_rewrite.
    unfold BottomUp.recursive_rewrite in r.  
    unfold BottomUp.recursive_rewrite' in r. 
    unfold Core.rw_bind in r.
    match goal with
    | H := context [@get_respectful ?a ?b ?c ?d ?e ?f ?g ?h ?i ?j ?k ?l ?m] |- _ =>
           let r := eval vm_compute in (@get_respectful a b c d e f g h i j k l m) in
                                        change (@get_respectful a b c d e f g h i j k l m) with r in H; cbv beta iota in H; idtac r
    end.
    Set Printing Depth 100.
    match goal with
    | H := context [@get_respectful ?a ?b ?c ?d ?e ?f ?g ?h ?i ?j ?k ?l ?m] |- _ =>
           let r := eval vm_compute in (@get_respectful a b c d e f g h i j k l m) in
                                        change (@get_respectful a b c d e f g h i j k l m) with r in H; cbv beta iota in H; idtac r
    end.
    
    unfold Core.rw_bind in r.
 Print get_respectful.
 Print Core.ResolveProper.
Check get_respectful func_unify
(@Inj (CoreTypes.ctyp typ') func
   {|
   SymOneOf.OneOfType.index := 3;
   SymOneOf.OneOfType.value := @ilf_entails typ
                                 (@CoreTypes.tyBase0 typ'
                                    {|
                                    TSymOneOf.OneOfType.indexF := 4;
                                    TSymOneOf.OneOfType.valueF := tAsn |}) |})
(@Rflip (CoreTypes.ctyp typ') (expr (CoreTypes.ctyp typ') func)
   (@Rinj (CoreTypes.ctyp typ') (expr (CoreTypes.ctyp typ') func)
      (@Inj (CoreTypes.ctyp typ') func
         (@fImpl (CoreTypes.ctyp typ') func ILogicView_func
            (@typ0 (CoreTypes.ctyp typ') (@RType_typ typ' TSym_typ') Prop Typ0_tyProp))))).

Print is_refl.
    rtac_debug.
    unfold PAPPLY in r.
    unfold RTac.PApply.PAPPLY in r.
    unfold AT_GOAL in r.
    match goal with 
    | H := context [PApply.get_lemma ?a ?b ?c] |- _ => 
           let r := eval vm_compute in (PApply.get_lemma a b c) in
                                        change (PApply.get_lemma a b c) with r in H; cbv beta iota in H
    end.
Check landexistsDR.    
    vm_compute in r.
    unfold PApply.get_lemma in r.
    unfold ILogicRewrite.rewrite_it in r.
    unfold Tactic.auto_setoid_rewrite_bu in r.
    rtac_debug.
Print AllSubst.
  match goal with
  | H := context [Polymorphic.inst ?a ?b] |- _ => 
         let r := eval vm_compute in (Polymorphic.inst a b) in 
         change (Polymorphic.inst a b) with r in H; cbv beta iota in H
  end.
  unfold PolyInst.get_types in r.
  match goal with 
  | H := context [func_unify ?a ?b ?c] |- _ => 
         let r := eval vm_compute in (func_unify a b c) in 
                                      idtac r
  end.
Print type_sym_unifier.
  unfold type_sym_unifier in r.
Set Printing All.
Set Printing Depth 100.
  Eval vm_compute in (@typeof_sym (CoreTypes.ctyp typ') Java.Func.Type.RType_typ func 
                           (@RSym_func fs)
                           (OneOfType.mkOneOf func_map (xI xH)
                              (@ilf_entails typ
                                 (@CoreTypes.tyBase0 typ'
                                    (TSymOneOf.OneOfType.mkOneOfF typ_map O (xO (xO xH)) tAsn))))
).
Print type_sym_unifier.
  match goal with 
  | H := 
    context [type_sym_unifier (CTypeUnify.ctype_unify_slow typ') ?a ?b ?c] |- _ =>
    let r := eval vm_compute in
    (type_sym_unifier (CTypeUnify.ctype_unify_slow typ') a b c) in 
        idtac r
  end.
Print CoreTypes.
  Print PolyInst.get_types.
  
  unfold plem_entails_refl in r.
  
  cbv beta iota in r.
  
  unfold PolyInst.build_vector in r.
  unfold plem_entails_refl in r.
  cbv beta iota in r.
  unfold Polymorphic.inst in r.
  match goal with
  | 


  simpl in r.

  match goal with 
  | H := context [PolyInst.get_types ?a ?b ?c ?d ?e ?f] |- _ => 
         let x := constr:(PolyInst.get_types a b c d e f) in
         let r := eval vm_compute in x in 
                                 idtac r
  end.
  simpl in r.
  unfold PolyInst.get_types in r.
Print TRY.
  
  rtac_debug.
  cbv iota beta in r.
  match goal with 
  | H : context [INTRO typ func (CTop nil nil) (TopSubst (expr typ func) nil nil) ?s] |- _ => idtac s
  
  end.
  unfold INTRO in r.
  unfold RTac.Intro.INTRO in r.
  unfold fintro in r.

  simpl in r.
Check 
  unfold (Then.THEN) in r.
  vm_compute in r.

Print plem_entails_refl.  
Print lem_entails_refl.  
  intros. Fuc
Print lem_entails_refl.
Locate Z.of_nat.
*)

Fixpoint mkSwapPre n : RFun (RFun string val) asn :=
	match n with
	  | 0   => empSP
	  | S n => ap_pointsto [("o": string ), (append "f" (nat2string10 n) : field),
	  	                     (eval (E_val (vint (BinInt.Z.of_nat n))))] **
	           mkSwapPre n
	end.


Fixpoint mkSwapPostAux n m : RFun (RFun string val) asn :=
  match n with
    | 0 => empSP
	| S n => ap_pointsto [("o": string), (append "f" (nat2string10 n) : field),
	  	                     (eval (E_val (vint (BinInt.Z.of_nat (m - (S n))))))] **
	         mkSwapPostAux n m
  end.

Definition mkSwapPost n : RFun (RFun string val) asn := mkSwapPostAux n n.

Fixpoint mkRead n c : cmd :=
	match n with
	  | 0 => c
	  | S n => cseq (cread ((append "x" (nat2string10 n):string)) ("o":string) ((append "f" (nat2string10 n)):field))
	                (mkRead n c)
    end.

Fixpoint mkWriteAux n m c :=
	match n with
	  | 0 => c
	  | S n => cseq (cwrite ("o":string) (append "f" (nat2string10 n)) (E_var (append "x" (nat2string10 (m - (S n))))))
	                (mkWriteAux n m c)
    end.

Definition mkWrite n c := mkWriteAux n n c.

Definition mkSwapProg (n : nat) (c : cmd) : cmd := mkRead n (mkWrite n c).

Definition mkSwap n : Prop :=
  ltrue |-- triple (mkSwapPre n) (mkSwapPost n) (mkSwapProg n cskip).

Set Printing Depth 100.

(*
Lemma test_swap :
|--
( {[ap_pointsto  ["o", ("f")%string, eval (E_val (vint 5))] **
    ap_pointsto  ["o", ("g")%string, eval (E_val (vint 6))] ** empSP]}
 ("x")%string R= "o" [("f")%string];;
 ("y")%string R= "o" [("g")%string];;
 "o" [("f")%string] W= E_var ("y")%string;;
 "o" [("g")%string] W=E_var ("x")%string;; Skip
 {[ap_pointsto  ["o", ("f")%string, eval (E_val (vint 6))] **
   ap_pointsto  ["o", ("g")%string, eval (E_val (vint 5))] ** empSP]} ).
Proof.
  Time run_rtac reify_java term_table (@runTac_sound rw_fail).
Qed.
*)

Definition mkSwap2 n :=
	ltrue |-- triple ltrue (mkSwapPost n) (mkSwapProg n cskip).


 

 End blurb.