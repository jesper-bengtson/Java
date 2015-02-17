Require Import MirrorCore.syms.SymEnv.
Require Import MirrorCore.Reify.Reify.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Lambda.ExprVariables.
Require Import MirrorCore.RTac.RTac.

Require Import Java.Func.JavaType.
Require Import Java.Func.JavaFunc.
Require Import Java.Func.Reify.
Require Import Java.Examples.ListModel.
Require Import Java.Examples.ListClass.
Require Import Java.Language.Lang.
Require Import Java.Logic.AssertionLogic.
Require Import Java.Tactics.SymEx.
Require Import Java.Semantics.OperationalSemantics.
Require Import Java.Tactics.Tactics.

Require Import Charge.ModularFunc.OpenFunc.
Require Import Charge.ModularFunc.ListFunc.
Require Import Charge.ModularFunc.ILogicFunc.
Require Import Charge.ModularFunc.BILogicFunc.
Require Import Charge.ModularFunc.BaseFunc.
Require Import Charge.SetoidRewrite.AutoSetoidRewrite.
Require Import Charge.SetoidRewrite.Base.
Require Import Charge.SetoidRewrite.ILSetoidRewrite.
Require Import Charge.SetoidRewrite.BILSetoidRewrite.
Require Import Charge.SetoidRewrite.EmbedSetoidRewrite.
Require Import Charge.Tactics.Rtac.Apply.
Require Import Charge.Tactics.Rtac.Intro.
Require Import Charge.Tactics.Rtac.Instantiate.
Require Import Charge.Tactics.Rtac.Cancellation.
Require Import Charge.Tactics.PullConjunct.ILPullConjunct.
Require Import Charge.Tactics.PullQuant.BILPullQuant.
Require Import Charge.Tactics.PullQuant.ILPullQuant.
Require Import Charge.Tactics.PullQuant.EmbedPullQuant.

Require Import ExtLib.Core.RelDec.

Set Printing Width 180.

Definition fList : expr typ JavaFunc.func := 
	Inj (inl (inl (inl (inl (inl (inl (inl (inl 1%positive)))))))).
Definition fNode : expr typ JavaFunc.func := 
	Inj (inl (inl (inl (inl (inl (inl (inl (inl 2%positive)))))))).

Definition mkList (p : var) (xs : expr typ JavaFunc.func) : expr typ JavaFunc.func:=
	 mkAps fList 
	 	((xs, tyList tyVal)::
	 	(((App (fStackGet (func := expr typ JavaFunc.func)) 
	 	(mkString (func := JavaFunc.func) p)), tyVal)::nil)) tyAsn.

Definition mkNode (p xs : expr typ JavaFunc.func) :=
	 mkAps fNode 
	 	((xs, tyList tyVal)::
	 	(p, tyVal)::nil) tyAsn.

Definition apCons t (p : var) (xs : expr typ JavaFunc.func) :=
	mkAps (fCons (func := expr typ JavaFunc.func) tyVal)
	 	((xs, tyList t)::
	 	(((App (fStackGet (func := expr typ JavaFunc.func)) 
	 	(mkString (func := JavaFunc.func) p)), tyVal)::nil)) (tyList t).

Definition rw_true (e : expr typ JavaFunc.func) 
	(rvars : list (RG (expr typ JavaFunc.func))) (rg : RG (expr typ JavaFunc.func)) :
 	m (expr typ JavaFunc.func) :=
  match e with
  	| App (App (Inj (inl (inl (inl (inl (inl (inl (inl (inr (ilf_and tySasn)))))))))) (Inj (inl (inl (inl (inl (inl (inl (inl (inr (ilf_true tySasn)))))))))))
         (Inj (inl (inl (inl (inl (inl (inl (inl (inr (ilf_true tySasn)))))))))) =>
         (rg_bind (unifyRG (@rel_dec (expr typ JavaFunc.func) _ _) rg (RGinj (fEntails tySasn)))
          (fun _ => rg_ret (mkTrue tySasn)))
    | _ => rg_fail
  end.
  	  
(* List rewrite rule type checks *)

Eval vm_compute in typeof_expr nil nil (mkExists tyVal tySasn 
	(mkStar tySasn (mkPointstoVar "x" "head" (mkConst tyVal (Var 0))) 
		(mkNode (mkConst tyVal (Var 0)) (mkConst (tyList tyVal) (mkNil tyVal))))).

(* Unfold predicate for list *)

Definition rw_unfold_list (e : expr typ JavaFunc.func) 
	(rvars : list (RG (expr typ JavaFunc.func))) (rg : RG (expr typ JavaFunc.func)) :
 	m (expr typ JavaFunc.func) :=
  match e with
    | App
        (App (Inj (inl (inl (inl (inr (of_ap (tyList tyVal) tyAsn))))))
           (App
              (App (Inj (inl (inl (inl (inr (of_ap tyVal (tyArr (tyList tyVal) tyAsn)))))))
                 (App (Inj (inl (inl (inl (inr (of_const (tyArr tyVal (tyArr (tyList tyVal) tyAsn))))))))
                    (Inj (inl (inl (inl (inl (inl (inl (inl (inl 1%positive)))))))))))
              (App (Inj (inl (inl (inl (inr of_stack_get))))) (Inj (inl (inl (inl (inl (inl (inr (pString p)))))))))))
        xs =>
          rg_plus
            (rg_bind (unifyRG (@rel_dec (expr typ JavaFunc.func) _ _) rg (RGinj (fEntails tySasn)))
              (fun _ => rg_ret (mkExists tyVal tySasn (mkStar tySasn (mkPointstoVar p "head" (mkConst tyVal (Var 0))) (mkNode (mkConst tyVal (Var 0)) (lift 0 1 xs))))
              	))
            (rg_bind (unifyRG (@rel_dec (expr typ JavaFunc.func) _ _) rg (RGflip (RGinj (fEntails tySasn))))
              (fun _ => rg_ret (mkExists tyVal tySasn (mkStar tySasn (mkPointstoVar p "head" (mkConst tyVal (Var 0))) (mkNode (mkConst tyVal (Var 0)) (lift 0 1 xs))))
              ))
    | App
         (App (Inj (inl (inl (inl (inr (of_ap (tyList tyVal) tyAsn))))))
            (App
               (App (Inj (inl (inl (inl (inr (of_ap tyVal (tyArr (tyList tyVal) tyAsn)))))))
                  (App (Inj (inl (inl (inl (inr (of_const (tyArr tyVal (tyArr (tyList tyVal) tyAsn)))))))) (Inj (inl (inl (inl (inl (inl (inl (inl (inl 2%positive)))))))))))
               p))
         (App
            (App (Inj (inl (inl (inl (inr (of_ap (tyList tyVal) (tyList tyVal)))))))
               (App
                  (App (Inj (inl (inl (inl (inr (of_ap tyVal (tyArr (tyList tyVal) (tyList tyVal))))))))
                     (App (Inj (inl (inl (inl (inr (of_const (tyArr tyVal (tyArr (tyList tyVal) (tyList tyVal))))))))) (Inj (inl (inl (inl (inl (inr (pCons tyVal)))))))))
                 x))
            xs)
        => rg_plus
            (rg_bind (unifyRG (@rel_dec (expr typ JavaFunc.func) _ _) rg (RGinj (fEntails tySasn)))
              (fun _ => rg_ret (mkExists tyVal tySasn (mkStar tySasn (mkPointsto (lift 0 1 p) "val" (lift 0 1 x)) 
              	(mkStar tySasn (mkPointsto (lift 0 1 p) "next" (mkConst tyVal (Var 0))) (mkNode (mkConst tyVal (Var 0)) (lift 0 1 xs)))))))
            (rg_bind (unifyRG (@rel_dec (expr typ JavaFunc.func) _ _) rg (RGflip (RGinj (fEntails tySasn))))
              (fun _ => rg_ret (mkExists tyVal tySasn (mkStar tySasn (mkPointsto (lift 0 1 p) "val" (lift 0 1 x)) 
              	(mkStar tySasn (mkPointsto (lift 0 1 p) "next" (mkConst tyVal (Var 0))) (mkNode (mkConst tyVal (Var 0)) (lift 0 1 xs)))))))
    | _ => rg_fail
  end.

(* List match works *)

Eval vm_compute in 
	match mkList "this" (mkConst (tyList tyVal) (mkConst tyVal (mkNil tyVal))) with
    | App
        (App (Inj (inl (inl (inl (inr (of_ap (tyList tyVal) tyAsn))))))
           (App
              (App (Inj (inl (inl (inl (inr (of_ap tyVal (tyArr (tyList tyVal) tyAsn)))))))
                 (App (Inj (inl (inl (inl (inr (of_const (tyArr tyVal (tyArr (tyList tyVal) tyAsn))))))))
                    (Inj (inl (inl (inl (inl (inl (inl (inl (inl 1%positive)))))))))))
              (App (Inj (inl (inl (inl (inr of_stack_get))))) 
                (Inj (inl (inl (inl (inl (inl (inr (pString "this")))))))))))
        xs => true
    | _ => false
    end.

Definition exists_body : expr typ func :=
  mkForall tyVal tyProp 
    (mkForall tyVal tyProp
    (mkEntails tyProp (mkTrue tyProp) 
    	(mkAnd tyProp (mkTrue tyProp) (mkExists tyVal tyProp (mkEq tyVal (Var 0) (Var 1)))))).

Eval vm_compute in (THEN (INTRO typ func) PULL_EXISTSR)
	 nil nil 0 0 (CTop nil nil) (ctx_empty (expr := expr typ JavaFunc.func)) exists_body.
Eval vm_compute in exists_body.

Require Import MirrorCore.Lambda.Red.

Definition blarf : expr typ func :=
App (Abs tyVal (App (App (Inj (inl (inl (inl (inl (inl (inr (pEq tyVal)))))))) 
	(ExprCore.Var 0)) (ExprCore.Var 8))) (Var 3).
Check beta.
Eval vm_compute in beta blarf.
Eval vm_compute in typeof_expr nil nil exists_body.

(* Rewriting with rw_true works *)

Eval vm_compute in 
  setoid_rewrite nil _ (fEntails : typ -> expr typ (JavaFunc.func)) rw_true
    (sr_combine il_respects
               (sr_combine (@il_respects_reflexive typ (JavaFunc.func) _ _ _ ilops _ _)
                                        (sr_combine bil_respects
                                                    (sr_combine eq_respects 
                                                    (sr_combine spec_respects refl)))))
    (fun _ => rw_fail) tySasn (mkAnd tySasn (mkTrue tySasn) (mkTrue tySasn)).

(* rewriting with rw_unfold_list does not *)

Eval vm_compute in
  setoid_rewrite nil _ (fEntails : typ -> expr typ (JavaFunc.func)) rw_unfold_list
    (sr_combine (il_respects (typ := typ) (func := JavaFunc.func))
               (sr_combine (@il_respects_reflexive typ (JavaFunc.func) _ _ _ ilops _ _)
                                        (sr_combine bil_respects
                                                    (sr_combine eq_respects 
                                                    (sr_combine spec_respects refl)))))
    (fun _ => rw_fail) tySasn (mkList "x" (mkConst (tyList tyVal) (mkNil tyVal))).

Require Import Charge.Logics.ILogic.
Require Import Java.Logic.SpecLogic.

Require Import ExtLib.Structures.Applicative.
Local Instance Applicative_Fun A : Applicative (Fun A) :=
{ pure := fun _ x _ => x
; ap := fun _ _ f x y => (f y) (x y)
}.



Notation "'ap_List' '[' x ',' xs ']'" := 
	(ap (T := Fun Lang.stack) (ap (T := Fun Lang.stack)
		(pure (T := Fun Lang.stack) List) (stack_get x)) 
			xs).


Notation "'ap_cons' '[' x ',' xs ']'" := 
	(ap (T := Fun Lang.stack) (ap (T := Fun Lang.stack)
		(pure (T := Fun Lang.stack) cons) x) xs).

Definition add_pre xs := ap_List ["this", pure (T := Fun Lang.stack) xs].
Definition add_post xs := ap_List ["this", ap_cons [stack_get "n", pure (T := Fun Lang.stack) xs]].

Definition add_body := 
      cseq (calloc "tn" "NodeC")
         (cseq (cwrite "tn" "val" (E_var "n"))
              (cseq (cread "lst" "this" "head")   
                    (cseq (cwrite "tn" "next" (E_var "lst"))
                          (cseq (cwrite "this" "head" (E_var "tn")) cskip)))).
Instance List_env : Environment := {
  java_env := 
    SymEnv.from_list
  	  (@SymEnv.F typ _ (tyArr tyVal (tyArr (tyList tyVal) tyAsn)) List::
  	   @SymEnv.F typ _ (tyArr tyVal (tyArr (tyList tyVal) tyAsn)) NodeList::nil) 
}.

Reify Seed Typed Table term_table += 1 => [ (tyArr tyVal (tyArr (tyList tyVal) tyAsn)) , List ].
Reify Seed Typed Table term_table += 2 => [ (tyArr tyVal (tyArr (tyList tyVal) tyAsn)) , NodeList ].

Lemma test_cons : forall (xs : list val) , |-- triple (add_pre xs) (add_post xs) add_body.
Proof.
  unfold add_pre, add_body, add_post.
  run_rtac reify_imp term_table (@runTac_sound List_env rw_unfold_list).

Definition testAdd :=
		(mkForall (tyList tyVal) tyProp
		  	(mkEntails tySpec (mkProgEq (mkProg ListProg))
		  	           (mkTriple (mkList "this" (mkConst (tyList tyVal) (Var 0)))
		  	           			 (mkCmd add_body)
		  	           			 (mkList "this" (apCons tyVal "n" (mkConst (tyList tyVal) (Var 0))))))).


Set Printing Depth 100.  	           		

Fixpoint goal_to_expr (g : Goal typ (expr typ func)) : list (expr typ func) :=
  match g with
    | GGoal e => e::nil
    | GSolved => nil
    | GExs _ _ g => goal_to_expr g
    | GHyp _ g => goal_to_expr g
    | GAll _ g => goal_to_expr g
    | GConj_ l r => (goal_to_expr l) ++ (goal_to_expr r)
  end.

Definition runTac2 (tac : expr typ JavaFunc.func) rw := 
     (THEN (THEN (THEN (THEN (THEN (THEN (THEN (REPEAT 1000 (INTRO typ JavaFunc.func)) (symE rw)) 
	(INSTANTIATE typ JavaFunc.func)) 
		(TRY (THEN (THEN (THEN (APPLY typ JavaFunc.func ent_exists_right_lemma) (INSTANTIATE typ JavaFunc.func))
			(INTRO typ JavaFunc.func)) BETA)))
	 (STEP_REWRITE rw))  PULL_EXISTSR)
		((THEN (THEN (THEN (APPLY typ JavaFunc.func ent_exists_right_lemma) (INSTANTIATE typ JavaFunc.func))
			(INTRO typ JavaFunc.func)) BETA)))
			
     (CANCELLATION typ func tySasn is_pure))
	 nil nil 0 0 (CTop nil nil) (ctx_empty (expr := expr typ JavaFunc.func)) tac.

Time Eval vm_compute in @runTac2 testAdd rw_unfold_list.
Locate PULL_EXISTSR.
Check mkList.


Time Eval vm_compute in 
	match (@runTac2 testAdd rw_unfold_list) with
		| More_ _ g => 
		  Some (match goalD nil nil g with
		          | Some _ => None
		          | _ => Some g
		        end
		       )
		| _ => None
	end.
