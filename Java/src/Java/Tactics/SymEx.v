Require Import Coq.Strings.String.
Require Import Coq.PArith.BinPos.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.String.
Require Import ExtLib.Data.Nat.
Require Import ExtLib.Data.HList.
Require Import MirrorCore.Lemma. 
Require Import MirrorCore.TypesI.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.RTac.RTac.
Require Import MirrorCore.provers.DefaultProver.
Require MirrorCore.syms.SymEnv.
Require MirrorCore.syms.SymSum.
Require Import MirrorCore.Subst.FMapSubst.
Require Import MirrorCore.Lambda.ExprLift.
Require Import MirrorCore.Lambda.ExprSubst.
Require Import MirrorCore.Lambda.ExprUnify_simul.
Require Import MirrorCore.Lambda.Red.
Require Import MirrorCore.Lambda.AppN. 
Require Import MirrorCore.Lambda.RedAll.
Require Import MirrorCore.Lambda.ExprVariables.
Require Import Charge.ModularFunc.ILogicFunc.
Require Import Charge.Tactics.OrderedCanceller.
Require Import Charge.Tactics.BILNormalize.
Require Import Charge.Tactics.SynSepLog.
Require Import Charge.Tactics.SepLogFold.

Require Import Java.Tactics.Semantics.
Require Import Java.Func.JavaType.
Require Import Java.Func.JavaFunc.

Require Import Charge.ModularFunc.BILogicFunc.

Require Import Charge.Tactics.Rtac.ReifyLemma.

Require Import Charge.Tactics.Rtac.PullConjunct.

Require Import MirrorCore.Reify.Reify.

Require Import Java.Func.Reify.

Require Import Charge.Tactics.Rtac.Subst.


Require Import Java.Language.Lang.
Require Import Java.Language.Program.
 
Require Import Charge.Tactics.Rtac.Apply.
Require Import Charge.Tactics.Rtac.Cancellation.
Require Import Charge.Tactics.Rtac.Intro.
Require Import Charge.Tactics.Rtac.EApply.
Require Import Charge.Tactics.Rtac.Instantiate.

Require Import Coq.Arith.Peano_dec.

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

Context {fs : Environment}.
          
Time Eval vm_compute in typeof_expr nil nil (cancelTest 10).
Check THEN.
Check runOnGoals.
Time Eval vm_compute in 
	(THEN (REPEAT 10 (INTRO typ func)) 
	(runOnGoals (CANCELLATION typ func tySasn is_pure))) 
		nil nil 0 0 (CTop nil nil) (ctx_empty (expr := expr typ func)) (cancelTest 10).

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

(** Skip **)
Definition skip_lemma : lemma typ (expr typ func) (expr typ func).
reify_lemma reify_imp rule_skip.
Defined.
Print skip_lemma.

Lemma skip_lemma_sound : 
	lemmaD (exprD'_typ0 (T:=Prop)) nil nil skip_lemma.
Proof.
  unfold lemmaD; simpl; intros.
  unfold exprT_App, exprT_Inj, Rcast_val, Rcast in * ; simpl in *.
  apply rule_skip. apply H.
Qed.

Example test_skip_lemma : test_lemma skip_lemma. Admitted.

Definition skip_lemma2 : lemma typ (expr typ func) (expr typ func).
reify_lemma reify_imp rule_skip2.
Defined.
Print skip_lemma2.

Example test_skip_lemma2 : test_lemma skip_lemma2. Admitted.

Definition seq_lemma (c1 c2 : cmd) : lemma typ (expr typ func) (expr typ func).
Proof.
  reify_lemma reify_imp (@rule_seq c1 c2).
Defined.
Print seq_lemma.

Lemma seq_lemma_sound c1 c2 : 
	lemmaD (exprD'_typ0 (T:=Prop)) nil nil (seq_lemma c1 c2).
Proof.
  unfold lemmaD; simpl; intros.
  unfold exprT_App, exprT_Inj, Rcast_val, Rcast in * ; simpl in *.
  eapply rule_seq; [apply H | apply H0].
Qed.

Example test_seq_lemma (c1 c2 : cmd) : test_lemma (seq_lemma c1 c2). Admitted.

Definition if_lemma (e : dexpr) (c1 c2 : cmd) : lemma typ (expr typ func) (expr typ func).
Proof.
  reify_lemma reify_imp (@rule_if e c1 c2).
Defined.

Require Import ExtLib.Tactics.
(*
Lemma if_lemma_sound e c1 c2 : 
	lemmaD (exprD'_typ0 (T:=Prop)) nil nil (if_lemma e c1 c2).
Proof.
  remember (exprD nil nil (evalDExpr e) tyExpr).
  Check rule_if.
  unfold lemmaD; simpl.
  unfold lemmaD', exprD'_typ0.
  unfold le
  unfold if_lemma.
  destruct o.
  unfold exprD in Heqo. simpl in Heqo.
  remember (ExprDsimul.ExprDenote.exprD' nil nil tyVal (evalDExpr e)).
  destruct o; inv_all; subst; try congruence.
  unfold lemmaD, lemmaD', exprD'_typ0, ExprDsimul.ExprDenote.exprD'; simpl in *; intros.
 unfold ExprDsimul.ExprDenote.exprD' in *; simpl in *; intros.
 unfold exprT_App, exprT_Inj, Rcast_val, Rcast in *; simpl in *.
 unfold OpenFunc.typ2_cast_bin, OpenFunc.typ3_cast_bin in *; simpl in *.
 unfold exprT, OpenT in *; simpl in *.
 rewrite <- Heqo0.
 unfold ExprDsimul.ExprDenote.exprD' in Heqo0. simpl in Heqo0.
 rewrite <- Heqo0.
 repeat red.
 setoid_rewrite <- Heqo.
 rewrite <- Heqo.
    unfold exprT_App, exprT_Inj, Rcast_val, Rcast in * ; simpl in *.
    eapply rule_if; [eapply H | eapply H0].
  + unfold lemmaD; simpl; intros.
    unfold exprT_App, exprT_Inj, Rcast_val, Rcast in * ; simpl in *.
    eapply rule_if; [eapply H | eapply H0].
  + unfold lemmaD; simpl; intros.
    unfold exprT_App, exprT_Inj, Rcast_val, Rcast in * ; simpl in *.
    eapply rule_if; [eapply H | eapply H0].

  Print if_lemma.
  vm_compute.
  unfold lemmaD'. simpl.
  unfold exprD'_typ0. simpl.
  unfold ExprDsimul.ExprDenote.exprD'.
  simpl.
  unfold if_lemma. simpl.
  apply rule_skip. apply H.
Qed.
*)
Example test_if_lemma e (c1 c2 : cmd) : test_lemma (if_lemma e c1 c2). Admitted.

Definition read_lemma (x y : var) (f : field) : lemma typ (expr typ func) (expr typ func).
Proof.  
  reify_lemma reify_imp (@rule_read_fwd x y f).
Defined.

Lemma read_lemma_sound x y f : 
	lemmaD (exprD'_typ0 (T:=Prop)) nil nil (read_lemma x y f).
Proof.
  (*
  unfold lemmaD; simpl; intros.
  unfold exprT_App, exprT_Inj, Rcast_val, Rcast, OpenFunc.typ3_cast_bin, OpenFunc.typ2_cast_bin, eq_rect_r in * ; simpl in *.
  eapply rule_read_fwd; [eapply H | eapply H0].
  *)
  admit.
Qed.


Example test_read_lemma x y f : test_lemma (read_lemma x y f). Admitted.

Set Printing Width 140.

Definition write_lemma (x : var) (f : field) (e : dexpr) : lemma typ (expr typ func) (expr typ func).
Proof.
  reify_lemma reify_imp (@rule_write_fwd x f e).
Defined.
(*
Lemma write_lemma_sound x f e : 
	lemmaD (exprD'_typ0 (T:=Prop)) nil nil (write_lemma x f e).
Proof.
  induction e.
  Check evalDExpr.
  unfold lemmaD, lemmaD'; simpl; intros.
  unfold exprT_App, exprT_Inj, Rcast_val, Rcast, OpenFunc.typ3_cast_bin, OpenFunc.typ2_cast_bin, eq_rect_r, 
  fPointsto, typ2_cast_bin, BaseFunc.mkString; simpl.
  unfold exprD'_typ0; simpl.
  unfold ExprDsimul.ExprDenote.exprD'; simpl.
  vm_compute.
  eapply rule_write_fwd; [eapply H | eapply H0].
Qed.
*)

Example test_write_lemma x f e : test_lemma (write_lemma x f e). Admitted.

Definition assign_lemma (x : var) (e : dexpr) : lemma typ (expr typ func) (expr typ func).
Proof.
  reify_lemma reify_imp (@rule_assign_fwd x e).
Defined.
Print assign_lemma.
Example test_assign_lemma x e : test_lemma (assign_lemma x e). Admitted.

Definition alloc_lemma (x : var) (C : class) : lemma typ (expr typ func) (expr typ func).
Proof.
  reify_lemma reify_imp (@rule_alloc_fwd x C).
Defined.
Example test_alloc_lemma x C : test_lemma (alloc_lemma x C). Admitted.

Definition pull_exists_lemma : lemma typ (expr typ func) (expr typ func).
Proof.
  reify_lemma reify_imp (@pull_exists val).
Defined.
Example test_pull_exists_lemma : test_lemma pull_exists_lemma. Admitted.
Eval vm_compute in pull_exists_lemma.

Definition ent_exists_right_lemma : lemma typ (expr typ func) (expr typ func).
Proof.
  reify_lemma reify_imp (@ent_left_exists val).
Defined.
Example test_pull_exists_lemma2 : test_lemma ent_exists_right_lemma. Admitted.

Definition eq_to_subst_lemma : lemma typ (expr typ func) (expr typ func).
Proof.
  reify_lemma reify_imp eq_to_subst.
Defined.
Eval vm_compute in eq_to_subst_lemma.
Example test_eq_lemma : test_lemma (eq_to_subst_lemma). Admitted.
Check rule_static_complete.
Definition scall_lemma (x : Lang.var) (C : class) (m : string) (es : list dexpr) 
  : lemma typ (expr typ func) (expr typ func).
Proof.
  reify_lemma reify_imp rule_static_complete.
Qed.

Print scall_lemma.

Print pull_exists_lemma.

Example test_pull_exists : test_lemma (pull_exists_lemma). Admitted.

Require Import Charge.ModularFunc.BaseFunc.

Require Import ExtLib.Tactics.

Require Import Charge.ModularFunc.ListFunc.

Require Import MirrorCore.Lambda.ExprTac.
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

Check apps.
Definition BETA := SIMPLIFY (typ := typ) (fun _ _ _ _ => beta_all (fun _ => @apps typ func)).

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
Qed.

Definition THEN' := @MirrorCore.RTac.Then.THEN typ (expr typ func).
Require Import Charge.Tactics.Rtac.Minify.

Let EAPPLY lem := THEN' (EAPPLY typ func lem) (MINIFY typ func).

Definition THEN (r1 r2 : rtac typ (expr typ func)) := 
  THEN (THEN (THEN (INSTANTIATE typ func) (runOnGoals r1)) (runOnGoals (INSTANTIATE typ func))) (runOnGoals r2).

Check SUBST.

Definition EQSUBST := THEN (EAPPLY eq_to_subst_lemma) (SUBST (ilp := ilp) (bilp := bilp) typ func).

(*
Notation "'ap_eq' '[' x ',' y ']'" :=
	 (ap (T := Fun stack) (ap (T := Fun stack) (pure (T := Fun stack) (@eq val)) x) y).
*)

Require Import Charge.ModularFunc.OpenFunc.
Require Import Charge.ModularFunc.BaseFunc.
Require Import Charge.ModularFunc.EmbedFunc.

Definition match_ap_eq (e : expr typ func) : bool :=
	match e with 
	  | App emb (App (App f (App (App g (App h e)) x)) y) =>
	  	match embedS emb, open_funcS f, open_funcS g, open_funcS h, baseS e with
	  		| Some (eilf_embed _ _), Some (of_ap _ _), Some (of_ap _ _), Some (of_const _), Some (pEq _) => true
	  		| _, _, _, _, _ => false
	  	end
	  | _ => false
	end.
Check @PULLCONJUNCTL.
Instance notehu : RelDec (@eq (expr typ func)).
apply RelDec_eq_expr.
apply _.
apply _.
split.
a

Definition PULLEQL := @PULLCONJUNCTL typ func RType_typ _ _ _ match_ap_eq _ _ _.

                        (*
	THEN (INSTANTIATE typ func subst) (runOnGoals (THEN (THEN (TRY FIELD_LOOKUP) 
		(runOnGoals (CANCELLATION typ func subst tySpec (fun _ => false)))) (runOnGoals FOLD))) ::
		solve_entailment :: nil).
	           *)
Require Import Charge.SetoidRewrite.AutoSetoidRewrite.
Require Import Charge.SetoidRewrite.Base.
Require Import Charge.SetoidRewrite.ILSetoidRewrite.
Require Import Charge.SetoidRewrite.BILSetoidRewrite.

  Definition spec_respects (e : expr typ func) (_ : list (RG (expr typ func)))
	   (rg : RG (expr typ func)) : m (expr typ func) :=
	   match e with
	     | Inj (inr pTriple) =>
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

Definition PULL_TRIPLE_EXISTS : rtac typ (expr typ func) :=
  THEN (THEN (EAPPLY pull_exists_lemma) (INTRO typ func)) BETA.

Definition solve_entailment (rw : rewriter (typ := typ) (func := func)) : rtac typ (expr typ func) :=
	THEN (INSTANTIATE typ func) 
		(FIRST (SOLVE (CANCELLATION typ func tySasn is_pure) ::
	           (THEN (THEN (THEN (THEN PULLEQL (REPEAT 1000 EQSUBST)) 
	           (STEP_REWRITE rw)) (REPEAT 1000 (INTRO typ func))) 
	              (CANCELLATION typ func tySasn is_pure)::
	           nil))).

Definition solve_alloc rw : rtac typ (expr typ func) :=
    THEN (INSTANTIATE typ func)
    (FIRST (SOLVE (CANCELLATION typ func tySpec (fun _ => false)) ::
                        FIELD_LOOKUP ::
                        THEN FOLD (solve_entailment rw) :: nil)).

Definition simStep (rw : rewriter (typ := typ) (func := func)) (r : rtac typ (expr typ func)) :=
    THEN (THEN (THEN (THEN (SUBST typ func)
    	(TRY PULL_TRIPLE_EXISTS)) (STEP_REWRITE rw)) (REPEAT 10 PULL_TRIPLE_EXISTS)) r.

Fixpoint tripleE (c : cmd) rw : rtac typ (expr typ func) :=
	match c with
	    | cskip => simStep rw (THEN (EAPPLY skip_lemma) (solve_entailment rw))
	    | calloc x C => simStep rw (THEN (EAPPLY (alloc_lemma x C)) 
	        (FIRST (solve_alloc rw::solve_entailment rw::nil)))
		| cseq c1 c2 => simStep rw (THEN' (EAPPLY (seq_lemma c1 c2))
		    (THENK (runOnGoals (TRY (tripleE c1 rw))) (THENK (MINIFY typ func) (runOnGoals (tripleE c2 rw)))))
		| cassign x e => simStep rw (THEN (EAPPLY (assign_lemma x e)) (solve_entailment rw))
		| cread x y f => simStep rw (THEN (EAPPLY (read_lemma x y f)) (solve_entailment rw))
		| cif e c1 c2 => simStep rw (THEN (EAPPLY (if_lemma e c1 c2)) (solve_entailment rw))
		| cwrite x f e => simStep rw (THEN (EAPPLY (write_lemma x f e)) (solve_entailment rw))
		| _ => IDTAC
	end.

Definition symE rw : rtac typ (expr typ func) :=
	(fun tus tvs n m ctx s e => 
		(match e return rtac typ (expr typ func) with 
			| App (App (Inj f) G) H =>
			  match ilogicS f, H with
			  	| Some (ilf_entails tySpec), (* tySpec is a pattern, should be checked for equality with tySpec *)
			  	  App (App (App (Inj (inr pTriple)) P) Q) (Inj (inr (pCmd c))) =>
			  	  	tripleE c rw
			  	| _, _ => FAIL
			  end
			| _ => FAIL
		end) tus tvs n m ctx s e).  

Definition runTac rw := 
   (THEN (THEN (REPEAT 1000 (INTRO typ func)) (symE rw)) 
	(INSTANTIATE typ func)).
	
Lemma runTac_sound rw : rtac_sound (runTac rw).
Proof.
  admit.
Qed.

Definition mkPointsto (x : expr typ func) (f : field) (e : expr typ func) : expr typ func :=
   mkAp tyVal tyAsn 
        (mkAp tyString (tyArr tyVal tyAsn)
              (mkAp tyVal (tyArr tyString (tyArr tyVal tyAsn))
                    (mkConst (tyArr tyVal (tyArr tyString (tyArr tyVal tyAsn))) 
                             fPointsto)
                    x)
              (mkConst tyString (mkString f)))
        e.
        
Require Import Java.Semantics.OperationalSemantics.
Require Import Java.Logic.SpecLogic.
Require Import Java.Logic.AssertionLogic.
Require Import Java.Examples.ListClass.
Require Import Charge.Logics.ILogic.

Fixpoint seq_skip n := 
	match n with
	  | 0 => cskip
	  | S n => cseq cskip (seq_skip n)
	end.

Require Import ExtLib.Structures.Applicative.
Local Instance Applicative_Fun A : Applicative (Fun A) :=
{ pure := fun _ x _ => x
; ap := fun _ _ f x y => (f y) (x y)
}.

Definition testSkip n : Prop :=
  forall (G : spec) (P : sasn), G |-- triple P P (seq_skip n).

Lemma INTRO_sound : rtac_sound (INTRO typ func).
Proof.
  admit.
Qed.

Require Import Java.Tactics.Tactics.
Check IDTAC_sound.

Ltac rtac_result reify term_table tac :=
	  let name := fresh "e" in
	  match goal with
	    | |- ?P => 
	      reify_aux reify term_table P name;
	      let t := eval vm_compute in (typeof_expr nil nil name) in
	      let goal := eval unfold name in name in 
	      match t with
	        | Some ?t =>
	          let goal_result := constr:(run_tac tac (GGoal name)) in 
	          let result := eval vm_compute in goal_result in 
	          idtac result
	        | None => idtac "expression " goal "is ill typed" t 
	      end
	  end.
	  
Lemma test_skip_lemma3 : testSkip 10.
Proof.
  idtac "start".
  unfold testSkip; simpl.
  
  Time run_rtac reify_imp term_table (@runTac_sound rw_fail).
Time Qed.

Definition test_alloc : expr typ func :=
	mkEntails tySpec (mkProgEq (mkProg ListProg))
		(mkTriple (mkTrue tySasn) (mkCmd (cseq (calloc "x" "NodeC") cskip)) (mkFalse tySasn)).

Require Import Charge.Logics.BILogic.
  
  Lemma test_alloc_correct : 
  prog_eq ListProg |-- triple empSP lfalse ((calloc "x" "NodeC");;Skip).
Proof.
  Time run_rtac reify_imp term_table (@runTac_sound rw_fail).
  unfold open_func_symD. simpl.
  admit.
Qed.

Lemma test_read : ltrue |-- 
    triple 
      (ap_pointsto [("o": var), ("f" : field), pure (T := Fun (Lang.stack)) (vint 3)] ** 
       ap_pointsto [("o": var), ("g" : field), pure (T := Fun (Lang.stack)) (vint 4)]) 
      (ap_pointsto [("o": var), ("f": field), pure (T := Fun (Lang.stack)) (vint 3)] ** 
      (ap_pointsto [("o": var), ("g": field), pure (T := Fun (Lang.stack)) (vint 4)]))
      (cseq (cread "x" "o" "f") (cseq (cread "y" "o" "g") cskip)).                    
Proof.
  Time run_rtac reify_imp term_table (@runTac_sound rw_fail).
Qed.

Lemma test_write :
	ltrue |--
	triple
      (ap_pointsto [("o": var), ("f" : field), pure (T := Fun (Lang.stack)) (vint 3)]) 
      (ap_pointsto [("o": var), ("f": field), pure (T := Fun (Lang.stack)) (vint 4)])
      (cseq (cwrite "o" "f" (E_val (vint 4))) cskip).                    
Proof.
  Time run_rtac reify_imp term_table (@runTac_sound rw_fail).
Qed.

Require Import BinInt.

Fixpoint mkSwapPre n : sasn :=
	match n with
	  | 0   => empSP
	  | S n => ap_pointsto [("o": Lang.var), (append "f" (nat2string10 n) : field), 
	  	                     (eval (E_val (vint (Z.of_nat n))))] **
	           mkSwapPre n
	end.  

	
Fixpoint mkSwapPostAux n m :=
  match n with
    | 0 => empSP
	| S n => ap_pointsto [("o": Lang.var), (append "f" (nat2string10 n) : field), 
	  	                     (eval (E_val (vint (Z.of_nat (m - (S n))))))] **
	         mkSwapPostAux n m
  end.           
  
Definition mkSwapPost n := mkSwapPostAux n n.

Fixpoint mkRead n c :=
	match n with
	  | 0 => c
	  | S n => cseq (cread ((append "x" (nat2string10 n):Lang.var)) ("o":Lang.var) ((append "f" (nat2string10 n)):field))
	                (mkRead n c)
    end.
						
Fixpoint mkWriteAux n m c :=
	match n with
	  | 0 => c
	  | S n => cseq (cwrite ("o":Lang.var) (append "f" (nat2string10 n)) (E_var (append "x" (nat2string10 (m - (S n))))))
	                (mkWriteAux n m c)
    end.

Definition mkWrite n c := mkWriteAux n n c.

Definition mkSwapProg (n : nat) (c : cmd) := mkRead n (mkWrite n c).
	
Definition mkSwap n :=
	ltrue |-- triple (mkSwapPre n) (mkSwapPost n) (mkSwapProg n cskip).

Set Printing Depth 100.

  Opaque ap.

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
  Time run_rtac reify_imp term_table (@runTac_sound rw_fail).
Qed.




Lemma test_skip_lemma4 : testSkip 10.
Proof.
  unfold testSkip; simpl.
  
  Time run_rtac reify_imp term_table (@runTac_sound rw_fail).
Time Qed.






Print rtac_sound.
Print rtac_spec.

Lemma test_swap2 : mkSwap 20.
Proof.
  unfold mkSwap, mkSwapPre, mkSwapPost, mkSwapProg, mkSwapPostAux, mkRead, mkWrite, mkWriteAux.
  
  Time run_rtac reify_imp term_table (@runTac_sound rw_fail).
Time Qed.
























































End blurb.

Instance EmptyEnv : Environment := {
  java_env := SymEnv.from_list nil
}.


Definition ASSUMPTION : rtac typ (expr typ func) :=
  EASSUMPTION (fun _ _ _ _ x y s => if x ?[ eq ] y then Some s else None).

Lemma ASSUMPTION_sound : rtac_sound ASSUMPTION.
Proof.
  admit.
Qed.

Ltac rtac_derive_soundness :=
  repeat first [ eapply IDTAC_sound
               | eapply ASSUMPTION_sound
               | eapply FAIL_sound
               | eapply INSTANTIATE_sound
               | eapply INTRO_sound
               | eapply FIRST_sound ; Forall_rtac_derive_soundness
               | eapply SOLVE_sound ; rtac_derive_soundness
               | eapply THEN_sound ;
                 [ rtac_derive_soundness
                 | rtacK_derive_soundness ]
               | eapply TRY_sound ; rtac_derive_soundness
               | eapply REPEAT_sound ; rtac_derive_soundness
               | eapply AT_GOAL_sound ; [ intros ; rtac_derive_soundness ]
               | eapply APPLY_sound ; [ simpl ] (* TODO(gmalecha): Needs to change *)
               | eapply EAPPLY_sound ; [ simpl ]  (* TODO(gmalecha): Needs to change *)
               ]
with rtacK_derive_soundness :=
  first [ solve [eauto]
        | eapply runOnGoals_sound ; rtac_derive_soundness
        ]
with Forall_rtac_derive_soundness :=
  repeat first [ 
                 eapply Forall_nil
               | eapply Forall_cons ;
                 [ try rtac_derive_soundness
                 | try Forall_rtac_derive_soundness ] ].


























Lemma LTrue : True.
Proof.
  apply I.
Qed.

Definition true_lemma : lemma typ (expr typ func) (expr typ func).
reify_lemma reify_imp LTrue.
Defined.
Print true_lemma.
(*
true_lemma = 
{| vars := nil; premises := nil; 
  concl := Inj (inl (inl (inl (inl (inl (inl (inl (inr (ilf_true tyProp))))))))) |}
     : lemma typ (expr typ func) (expr typ func)
*)
Lemma true_lemma_sound : 
	lemmaD (exprD'_typ0 (T:=Prop)) nil nil true_lemma.
Proof.
  compute.
  apply LTrue.
Qed.

Definition AUTO := APPLY typ func true_lemma.

Lemma AUTO_sound : rtac_sound AUTO.
Proof.
  admit.
Qed.

Lemma test_true : True.
Proof.
  run_rtac reify_imp term_table AUTO_sound.
Qed.
  
Print test_true.




(*

test_true = 
let tbl := FMapPositive.PositiveMap.Leaf (SymEnv.function RType_typ) in
let e := mkTrue tyProp in
run_rtac_Solved AUTO (TopSubst (expr typ func) nil nil) e AUTO_sound
  (eq_refl<:run_tac AUTO (GGoal (mkTrue tyProp)) = Solved (TopSubst (expr typ func) nil nil))
     : True

*)











Lemma andI (P Q : Prop) (HP : P) (HQ : Q) : P /\ Q.
Proof.
  tauto.
Qed.

Definition andI_lemma : lemma typ (expr typ func) (expr typ func).
Proof.
  reify_lemma reify_imp andI.
Defined.
Print andI_lemma.
Lemma andI_lemma_sound : 
	lemmaD (exprD'_typ0 (T:=Prop)) nil nil andI_lemma.
Proof.
  compute. intros. apply andI. assumption. assumption.
Qed.

Definition AUTO' := 
  THEN (REPEAT 10 (INTRO typ func)) 
    (FIRST (THEN (APPLY typ func andI_lemma) ASSUMPTION ::
      (APPLY typ func true_lemma) :: ASSUMPTION :: nil)).
    
Lemma AUTO'_sound : rtac_sound AUTO'.
Proof.
  unfold AUTO'.
  rtac_derive_soundness.
  admit.
  admit.
Qed.

Lemma test_and : forall (P Q R : Prop), Q -> P -> R -> P /\ Q.
Proof.
  run_rtac reify_imp term_table AUTO'_sound.
Qed.

Print test_and.
























Lemma orI1 (P Q : Prop) (HP : P) : P \/ Q.
Proof.
  tauto.
Qed.

Lemma orI2 (P Q : Prop) (HQ : Q) : P \/ Q.
Proof.
  tauto.
Qed.

Definition orI1_lemma : lemma typ (expr typ func) (expr typ func).
Proof.
  reify_lemma reify_imp orI1.
Defined.

Definition orI2_lemma : lemma typ (expr typ func) (expr typ func).
Proof.
  reify_lemma reify_imp orI2.
Defined.

Lemma orI1_lemma_sound : 
	lemmaD (exprD'_typ0 (T:=Prop)) nil nil orI1_lemma.
Proof.
  compute. intros. apply orI1. assumption.
Qed.

Lemma orI2_lemma_sound : 
	lemmaD (exprD'_typ0 (T:=Prop)) nil nil orI1_lemma.
Proof.
  compute. intros. apply orI1. assumption.
Qed.

Definition AUTO'' := 
  REC 20
    (fun rec => THEN (REPEAT 10 (INTRO typ func)) 
      (FIRST 
        (THEN (APPLY typ func andI_lemma) rec ::
        (THEN (APPLY typ func orI1_lemma) rec) ::
        (THEN (APPLY typ func orI2_lemma) rec) ::
        (APPLY typ func true_lemma) :: ASSUMPTION :: nil)))
    FAIL.
    
Lemma AUTO''_sound : rtac_sound AUTO''.
Proof.
  unfold AUTO''.
  (* rtac_derive_soundness. *)
  admit.
Qed.

Lemma test_and2 : forall (P Q R T : Prop),
	 Q -> P -> R -> (P /\ Q /\ R) \/
	    (Q /\ T /\ (R /\ R) /\ (P /\ Q) /\ Q).
Proof.
  run_rtac reify_imp term_table AUTO''_sound.
Qed.
(*
Ltac run_rtac reify term_table tac_sound :=
  match type of tac_sound with
    | rtac_sound ?tac =>
	  let name := fresh "e" in
	  match goal with
	    | |- ?P => 
	      reify_aux reify term_table P name;
	      let t := eval vm_compute in (typeof_expr nil nil name) in
	      let goal := eval unfold name in name in
	      match t with
	        | Some ?t =>
	          let goal_result := constr:(run_tac tac (GGoal name)) in 
	          let result := eval vm_compute in goal_result in
	          match result with
	            | More_ ?s ?g => 
	              cut (goalD_Prop nil nil g); [
	                let goal_resultV := g in
	               (* change (goalD_Prop nil nil goal_resultV -> exprD_Prop nil nil name);*)
	                exact_no_check (@run_rtac_More _ tac _ _ _ tac_sound
	                	(@eq_refl (Result (CTop nil nil)) (More_ s goal_resultV) <:
	                	   run_tac tac (GGoal goal) = (More_ s goal_resultV)))
	                | cbv_denote
	              ]
	            | Solved ?s =>
	              exact_no_check (@run_rtac_Solved _ tac s name tac_sound 
	                (@eq_refl (Result (CTop nil nil)) (Solved s) <: run_tac tac (GGoal goal) = Solved s))
	            | Fail => idtac "Tactic" tac "failed."
	            | _ => idtac "Error: run_rtac could not resolve the result from the tactic :" tac
	          end
	        | None => idtac "expression " goal "is ill typed" t
	      end
	  end
	| _ => idtac tac_sound "is not a soudness theorem."
  end.
  *)
Require Import Charge.Tactics.Rtac.PullQuant.
  
Lemma PULL_EXISTSL_sound : rtac_sound (THEN (REPEAT 10 (INTRO typ func)) (PULL_EXISTSL typ func ilops)).
Proof.
  admit.
Qed.

Lemma test_pull_quant_left  (P : sasn) (Q : nat -> sasn) :
  P //\\ (Exists x : nat, Q x) |-- P.
Proof.
  run_rtac reify_imp term_table PULL_EXISTSL_sound.
  
  Print func.
