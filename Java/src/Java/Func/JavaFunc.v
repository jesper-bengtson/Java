Require Import ChargeCore.Open.Subst.
Require Import ChargeCore.Open.Open.
Require Import ChargeCore.Open.Stack.
Require Import ChargeCore.Logics.BILogic.
Require Import Charge.Views.ILogicView.
Require Import Charge.Views.BILogicView.
Require Import Charge.Views.SubstView.
Require Import Charge.Views.EmbedView.

Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Data.String.
Require Import ExtLib.Data.Sum.
Require Import ExtLib.Data.Positive.
Require Import ExtLib.Data.SumN.
Require Import ExtLib.Data.Map.FMapPositive.
Require Import ExtLib.Tactics.Consider.

Require Import MirrorCore.TypesI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.Lemma.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Views.FuncView.
Require Import MirrorCore.syms.SymEnv.
Require Import MirrorCore.syms.SymSum.
Require Import MirrorCore.syms.SymOneOf.
Require Import MirrorCore.Subst.FMapSubst.
Require Import MirrorCore.Views.ListView.
Require Import MirrorCore.Views.ProdView.
Require Import MirrorCore.Views.ApplicativeView.
Require Import MirrorCore.Views.NatView.
Require Import MirrorCore.Views.StringView.

Require Import Java.Logic.AssertionLogic.
Require Import Java.Logic.SpecLogic.
Require Import Java.Language.Lang.
Require Import Java.Language.Program.
Require Import Java.Semantics.OperationalSemantics.
Require Import Java.Func.JavaType.

Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool.

Set Implicit Arguments.
Set Strict Implicit.

Inductive java_func :=
| pProg (p : Program)
| pMethod (m : Method)
| pVal (v : val)
| pCmd (c : cmd)
| pExpr (e : dexpr)
| pFields (f : list string)
          
| pMethodSpec
| pProgEq
| pTriple
| pTypeOf
| pFieldLookup
| pMethodLookup
    
| pPointsto
| pNull
    
| pMethodBody
| pMethodArgs
| pMethodRet
    
    
| pPlus
| pMinus
| pTimes
| pAnd
| pOr
| pNot
| pLt
| pValEq.

Fixpoint beq_list {A} (f : A -> A -> bool) (xs ys : list A) :=
  match xs, ys with
  | nil, nil => true
  | x::xs, y :: ys => andb (f x y) (beq_list f xs ys)
  | _, _ => false
  end.

Definition typeof_java_func bf :=
  match bf with
  | pProg _ => Some tyProg
  | pCmd _ => Some tyCmd
  | pMethod _ => Some tyMethod
  | pVal _ => Some tyVal
  | pExpr _ => Some tyDExpr
  | pFields _ => Some (tyList tyString)
		      
  | pMethodSpec => Some (tyArr tyString (tyArr tyString (tyArr tyVarList
		    	                                       (tyArr tyString (tyArr tySasn (tyArr tySasn tySpec))))))
  | pProgEq => Some (tyArr tyProg tySpec)
  | pTriple => Some (tyArr tySasn (tyArr tySasn (tyArr tyCmd tySpec)))
		    
  | pTypeOf => Some (tyArr tyString (tyArr tyVal tyProp))
		    
  | pFieldLookup => Some (tyArr tyProg (tyArr tyString (tyArr tyFields tyProp)))
  | pMethodLookup => Some (tyArr tyProg (tyArr tyString (tyArr tyString (tyArr tyMethod tyProp))))
		    
  | pPointsto => Some (tyArr tyVal (tyArr tyString (tyArr tyVal tyAsn)))
  | pNull => Some tyVal
		  
  | pMethodBody => Some (tyArr tyMethod tyCmd)
  | pMethodArgs => Some (tyArr tyMethod (tyList tyString))
  | pMethodRet => Some (tyArr tyMethod tyDExpr)
		       
  | pPlus => Some (tyArr tyVal (tyArr tyVal tyVal))
  | pMinus => Some (tyArr tyVal (tyArr tyVal tyVal))
  | pTimes => Some (tyArr tyVal (tyArr tyVal tyVal))
  | pAnd => Some (tyArr tyVal (tyArr tyVal tyVal))
  | pOr => Some (tyArr tyVal (tyArr tyVal tyVal))
  | pNot => Some (tyArr tyVal tyVal)
  | pLt => Some (tyArr tyVal (tyArr tyVal tyVal))
  | pValEq => Some (tyArr tyVal (tyArr tyVal tyVal))
  end.

Definition java_func_eq (a b : java_func) : option bool :=
  match a , b with
  | pProg p1, pProg p2 => Some (p1 ?[ eq ] p2)
  | pMethod m1, pMethod m2 => Some (m1 ?[ eq ] m2)
  | pVal v1, pVal v2 => Some (v1 ?[ eq ] v2)
  | pExpr e1, pExpr e2 => Some (e1 ?[ eq ] e2)
  | pFields f1, pFields f2 => Some (f1 ?[ eq ] f2)
  | pCmd c1, pCmd c2 => Some (c1 ?[ eq ]c2)
	                     
  | pMethodSpec, pMethodSpec => Some true
  | pProgEq, pProgEq => Some true
  | pTriple, pTriple => Some true
	                     
  | pTypeOf, pTypeOf => Some true
	                     
  | pPointsto, pPointsto => Some true
  | pFieldLookup, pFieldLookup => Some true
  | pMethodLookup, pMethodLookup => Some true
	                                 
  | pMethodBody, pMethodBody => Some true
  | pMethodArgs, pMethodArgs => Some true
  | pMethodRet, pMethodRet => Some true
	                           
  | pNull, pNull => Some true
  | pPlus, pPlus => Some true
  | pMinus, pMinus => Some true
  | pTimes, pTimes => Some true
  | pAnd, pAnd => Some true
  | pOr, pOr => Some true
  | pNot, pNot => Some true
  | pLt, pLt => Some true
  | pValEq, pValEq => Some true
  | _, _ => None
  end.

Global Instance RelDec_java_func : RelDec (@eq java_func) := 
  {
    rel_dec a b := match java_func_eq a b with 
    	  	   | Some b => b 
    		   | None => false 
    		   end
  }.

Global Instance RelDec_Correct_java_func : RelDec_Correct RelDec_java_func.
Proof.
  constructor.
  destruct x; destruct y; simpl;
  try solve [ try rewrite Bool.andb_true_iff ;
              repeat rewrite rel_dec_correct; intuition congruence ].                  	
Qed.
(*
Definition set_fold_fun (x : String.string) (f : field) (P : sasn) :=
	(liftn pointsto) (x/V) `f `null ** P.
*)
Definition java_func_symD bf :=
  match bf as bf return match typeof_java_func bf with
			| Some t => typD t
			| None => unit
			end with
    
  | pProg p => p
  | pMethod m => m
  | pVal v => v
  | pExpr e => e
  | pFields f => f
  | pCmd c => c
  | pMethodSpec => method_spec
  | pProgEq => prog_eq
  | pTriple => triple
                 
  | pTypeOf => typeof
                 
  | pFieldLookup => field_lookup
  | pMethodLookup => method_lookup
                       
  | pPointsto => pointsto
                   
  | pNull => null
               
  | pMethodBody => m_body
  | pMethodArgs => m_params
  | pMethodRet => m_ret
                    
  | pPlus => eplus
  | pMinus => eminus
  | pTimes => etimes
  | pAnd => eand
  | pOr => eor
  | pNot => enot
  | pLt => elt
  | pValEq => eeq
  end.

Global Instance RSym_JavaFunc : SymI.RSym java_func := 
  {
    typeof_sym := typeof_java_func;
    symD := java_func_symD;
    sym_eqb := java_func_eq
  }.

Global Instance RSymOk_JavaFunc : SymI.RSymOk RSym_JavaFunc.
Proof.
  split; intros.
  destruct a, b; simpl; try apply I; try reflexivity.
  consider (p ?[ eq ] p0); intros; subst; intuition congruence.
  consider (m ?[ eq ] m0); intros; subst; intuition congruence.
  consider (v ?[ eq ] v0); intros; subst; intuition congruence.
  consider (c ?[ eq ] c0); intros; subst; intuition congruence.
  consider (e ?[ eq ] e0); intros; subst; intuition congruence.
  consider (f ?[ eq ] f0); intros; subst; intuition congruence.
Qed.	

Fixpoint list_to_pmap_aux {T : Type} (lst : list T) (p : positive) : pmap T :=
  match lst with
    | nil => Empty
    | x :: xs => pmap_insert p x (list_to_pmap_aux xs (p + 1))
  end.
  
Definition list_to_pmap {T : Type} (lst : list Type) := list_to_pmap_aux lst 1.

Definition func_map : pmap Type :=
	list_to_pmap (T := Type) 
	  (java_func::SymEnv.func::@ilfunc typ::@bilfunc typ::@list_func typ::
	   @subst_func typ::@embed_func typ::(natFunc:Type)::(stringFunc:Type)::
           @prod_func typ::@ap_func typ::nil).

Definition func := OneOf func_map.

Global Instance ILogicView_func : FuncView func (@ilfunc typ) :=
  FuncViewPMap 3func_map eq_refl.
Global Instance BILogicView_func : FuncView func (@bilfunc typ) :=
  FuncViewPMap 4 func_map eq_refl.
Global Instance ListView_func : FuncView func (@list_func typ) :=
  FuncViewPMap 5 func_map eq_refl.
Global Instance SubstView_func : FuncView func (@subst_func typ) :=
  FuncViewPMap 6 func_map eq_refl.
Global Instance EmbedView_func : FuncView func (@embed_func typ) :=
  FuncViewPMap 7 func_map eq_refl.
Global Instance NatView_func : FuncView func natFunc :=
  FuncViewPMap 8 func_map eq_refl.
Global Instance StringView_func : FuncView func stringFunc :=
  FuncViewPMap 9 func_map eq_refl.
Global Instance ProdView_func : FuncView func (@prod_func typ) :=
  FuncViewPMap 10 func_map eq_refl.
Global Instance ApplicativeView_func : FuncView func (@ap_func typ) :=
  FuncViewPMap 11 func_map eq_refl.

Section MakeJavaFunc.

  Definition mkJavaFunc (f : java_func) : expr typ func := 
    Inj (Into (ts := func_map) f 1 eq_refl).

  Definition mkVal v : expr typ func := mkJavaFunc (pVal v).
  Definition mkProg P : expr typ func := mkJavaFunc (pProg P).
  Definition mkMethod M : expr typ func := mkJavaFunc (pMethod M).
  Definition mkCmd c : expr typ func := mkJavaFunc (pCmd c).
  Definition mkDExpr e : expr typ func := mkJavaFunc (pExpr e).
  Definition mkFields f : expr typ func := mkJavaFunc (pFields f).
  
  Definition fMethodSpec : expr typ func := mkJavaFunc pMethodSpec.
  Definition fProgEq : expr typ func := mkJavaFunc pProgEq.
  Definition fTriple : expr typ func := mkJavaFunc pTriple.
  Definition fTypeOf : expr typ func := mkJavaFunc pTypeOf.
  Definition fFieldLookup : expr typ func := mkJavaFunc pFieldLookup.
  Definition fMethodLookup : expr typ func := mkJavaFunc pMethodLookup.
  Definition fPointsto : expr typ func := mkJavaFunc pPointsto.
  Definition mkNull : expr typ func := mkJavaFunc pNull.
  
  Definition fMethodBody : expr typ func := mkJavaFunc pMethodBody.
  Definition fMethodArgs : expr typ func := mkJavaFunc pMethodArgs.
  Definition fMethodRet : expr typ func := mkJavaFunc pMethodRet.	
  
  Definition fPlus : expr typ func := mkJavaFunc pPlus.
  Definition fMinus : expr typ func := mkJavaFunc pMinus.
  Definition fTimes : expr typ func := mkJavaFunc pTimes.
  Definition fAnd : expr typ func := mkJavaFunc pAnd.
  Definition fOr : expr typ func := mkJavaFunc pOr.
  Definition fNot : expr typ func := mkJavaFunc pNot.
  Definition fLt : expr typ func := mkJavaFunc pLt.
  Definition fValEq : expr typ func := mkJavaFunc pValEq.

  Definition mkTriple P c Q : expr typ func := App (App (App fTriple P) Q) c.
  Definition mkFieldLookup P C f : expr typ func := App (App (App fFieldLookup P) C) f.
  Definition mkTypeOf C x : expr typ func := App (App fTypeOf C) x.
  Definition mkProgEq P := App fProgEq P.
  
  Definition mkMethodBody (M : Method) : expr typ func := App fMethodBody (mkMethod M).
  Definition mkMethodArgs (M : Method) : expr typ func := App fMethodArgs (mkMethod M).
  Definition mkMethodRet (M : Method) : expr typ func := App fMethodRet (mkMethod M).

	
  Definition mkExprList es :=
    (fold_right (fun (e : dexpr) (acc : expr typ func) => 
		   mkCons tyExpr (mkDExpr e) acc) (mkNil tyExpr) es).

Check @fStackGet.

Fixpoint evalDExpr (e : dexpr) : expr typ func :=
    match e with
    | E_val v => mkVal v
    | E_var x => App (Inj fStackGet) (mkString x)
    | E_plus e1 e2 => mkAps fPlus ((evalDExpr e2, tyVal)::(evalDExpr e1, tyVal)::nil) tyVal
    | E_minus e1 e2 => mkAps fMinus ((evalDExpr e2, tyVal)::(evalDExpr e1, tyVal)::nil) tyVal
    | E_times e1 e2 => mkAps fTimes ((evalDExpr e2, tyVal)::(evalDExpr e1, tyVal)::nil) tyVal
    | E_and e1 e2 => mkAps fAnd ((evalDExpr e2, tyVal)::(evalDExpr e1, tyVal)::nil) tyVal
    | E_or e1 e2 => mkAps fOr ((evalDExpr e2, tyVal)::(evalDExpr e1, tyVal)::nil) tyVal
    | E_not e => mkAps fNot ((evalDExpr e, tyVal)::nil) tyVal
    | E_lt e1 e2 => mkAps fLt ((evalDExpr e2, tyVal)::(evalDExpr e1, tyVal)::nil) tyVal
    | E_eq e1 e2 => mkAps fValEq ((evalDExpr e2, tyVal)::(evalDExpr e1, tyVal)::nil) tyVal
    end.

End MakeJavaFunc.


Class Environment := { java_env :> @SymEnv.functions typ _}.

Section JavaFunc.

  Context {fs : Environment}.

(* This needs to be parametric. It shouldn't be here 
Definition fs : @SymEnv.functions typ _ :=
  SymEnv.from_list
  	(@SymEnv.F typ _ (tyArr tyVal (tyArr (tyList tyVal) tyAsn)) List::
  	 @SymEnv.F typ _ (tyArr tyVal (tyArr (tyList tyVal) tyAsn)) NodeList::nil). 

*)
Check RSym.

  Global Instance RSym_ilfunc : RSym (@ilfunc typ) := 
	  RSym_ilfunc ilops.
  Global Instance RSym_bilfunc : RSym (@bilfunc typ) := 
	  RSym_bilfunc bilops.
  Global Instance RSym_embed_func : RSym (@embed_func typ) :=
	  RSym_embed_func eops.
(*  Global Instance RSym_later_func : RSym (@later_func typ) :=
	  RSym_later_func _ lops.*)
(*
  Global Instance RelDec_func : RelDec (@eq func).
  repeat apply RelDec_eq_pair; try apply _.
  apply _.
*)
(*
  Global Instance RSym_open_func : RSym (@subst_func typ) :=
	  @RSym_SubstFunc _ _ _ _ _ _ _ RType_typ _ _ _ _ _ _.
*)
  Global Existing Instance RSym_sum.
  Global Existing Instance RSymOk_sum.

  Definition RSym_sub_func (p : positive) :
    RSym (match pmap_lookup' func_map p with | Some T => T | None => Empty_set end).
  Proof.
    destruct p; simpl; [| | apply _].
    destruct p; simpl; [| | apply _].
    destruct p; simpl; [| | apply _].
    induction p; simpl; intuition; apply RSym_Empty_set.
    destruct p; simpl; [| | apply _].
    induction p; simpl; intuition; apply RSym_Empty_set.
    induction p; simpl; intuition; apply RSym_Empty_set.
    destruct p; simpl; [| | apply _].
    induction p; simpl; intuition; apply RSym_Empty_set.
    destruct p; simpl; [| | apply _].
    induction p; simpl; intuition; apply RSym_Empty_set.
    induction p; simpl; intuition; apply RSym_Empty_set.
    destruct p; simpl; [| | apply RSym_func; apply fs].
    destruct p; simpl; [| | apply RSym_SubstFunc].
    induction p; simpl; intuition; apply RSym_Empty_set.
    destruct p; simpl; [| | apply _].
    induction p; simpl; intuition; apply RSym_Empty_set.
    induction p; simpl; intuition; apply RSym_Empty_set.
    destruct p; simpl; [| | apply _].
    induction p; simpl; intuition; apply RSym_Empty_set.
    destruct p; simpl; [| | apply _].
    induction p; simpl; intuition; apply RSym_Empty_set.
    induction p; simpl; intuition; apply RSym_Empty_set.
  Defined.
Print RSymOk.
Instance RSymOk_Empty_set : RSymOk RSym_Empty_set := {
  sym_eqbOk a b :=
    match a return (match sym_eqb a b with 
                    | Some true => a = b 
                    | Some false => a <> b
                    | None => True
                    end) with
      end
    
}.

  Lemma RSymOk_sub_func (p : positive) : RSymOk (RSym_sub_func p).
  Proof.
    destruct p; simpl; [| | apply _].
    destruct p; simpl; [| | apply _].
    destruct p; simpl; [| | apply _].
    induction p; simpl; intuition; apply RSymOk_Empty_set.
    destruct p; simpl; [| | apply _].
    induction p; simpl; intuition; apply RSymOk_Empty_set.
    induction p; simpl; intuition; apply RSymOk_Empty_set.
    destruct p; simpl; [| | apply _].
    induction p; simpl; intuition; apply RSymOk_Empty_set.
    destruct p; simpl; [| | apply _].
    induction p; simpl; intuition; apply RSymOk_Empty_set.
    induction p; simpl; intuition; apply RSymOk_Empty_set.
    destruct p; simpl; [| | apply _].
    destruct p; simpl; [| | apply _].
    induction p; simpl; intuition; apply RSymOk_Empty_set.
    destruct p; simpl; [| | apply _].
    induction p; simpl; intuition; apply RSymOk_Empty_set.
    induction p; simpl; intuition; apply RSymOk_Empty_set.
    destruct p; simpl; [| | apply _].
    induction p; simpl; intuition; apply RSymOk_Empty_set.
    destruct p; simpl; [| | apply _].
    induction p; simpl; intuition; apply RSymOk_Empty_set.
    induction p; simpl; intuition; apply RSymOk_Empty_set.
  Defined.

  Global Instance RSym_func : RSym func := RSymOneOf func_map RSym_sub_func.
  
  Global Instance RSymOk_func : RSymOk RSym_func := RSymOk_OneOf func_map RSym_sub_func RSymOk_sub_func.

  Global Instance Expr_expr : ExprI.Expr _ (expr typ func) := @Expr_expr typ func _ _ _.
  Global Instance Expr_ok : @ExprI.ExprOk typ RType_typ (expr typ func) Expr_expr := @ExprOk_expr _ _ _ _ _ _ _ _.

  Require Import MirrorCore.VariablesI.
  Require Import MirrorCore.Lambda.ExprVariables.

  Global Instance ExprVar_expr : ExprVar (expr typ func) := _.
  Global Instance ExprVarOk_expr : ExprVarOk ExprVar_expr := _.

  Global Instance ExprUVar_expr : ExprUVar (expr typ func) := _.
  Global Instance ExprUVarOk_expr : ExprUVarOk ExprUVar_expr := _.

  Definition subst : Type :=
    FMapSubst.SUBST.raw (expr typ func).
  Global Instance SS : SubstI.Subst subst (expr typ func) :=
    @FMapSubst.SUBST.Subst_subst _.
  Global Instance SU : SubstI.SubstUpdate subst (expr typ func) :=
    @FMapSubst.SUBST.SubstUpdate_subst _ _ _ _. 
  Global Instance SO : SubstI.SubstOk SS := 
    @FMapSubst.SUBST.SubstOk_subst typ RType_typ (expr typ func) _.
  Global Instance SUO :SubstI.SubstUpdateOk SU SO :=  @FMapSubst.SUBST.SubstUpdateOk_subst typ RType_typ (expr typ func) _ _.
(*
  Global Instance MA : MentionsAny (expr typ func) := {
    mentionsAny := ExprCore.mentionsAny
  }.

  Global Instance MAOk : MentionsAnyOk MA _ _.
  Proof.
    admit.
  Qed.
*)
(*
  Lemma evalDexpr_wt (e : dexpr) : 
	  typeof_expr nil nil (evalDExpr e) = Some tyExpr.
  Proof. 
    (* Not true anymore, need to fix *)

    induction e.
    + simpl. admit.
    + simpl; reflexivity.
    + simpl. rewrite IHe1.
simpl; rewrite IHe1, IHe2; reflexivity.
    + simpl; rewrite IHe1, IHe2; reflexivity.
    + simpl; rewrite IHe1, IHe2; reflexivity.
    + simpl; rewrite IHe1, IHe2; reflexivity.
    + simpl; rewrite IHe1, IHe2; reflexivity.
    + simpl; rewrite IHe; reflexivity.
    + simpl; rewrite IHe1, IHe2; reflexivity.
    + simpl; rewrite IHe1, IHe2; reflexivity.
  Qed.
*)
(*
  Definition is_pure (e : expr typ func) : bool :=
	match e with
	  | App f P => match embedS f with
				     | Some (eilf_embed tyPure tySasn) => true
					 | Some (eilf_embed tyProp tySasn) => true
					 | _ => false
				   end
			
 	  | e =>
 		match ilogicS e with
 		  | Some (ilf_true _) => true
 		  | Some (ilf_false _) => true
 		  | _ => false
 		end
   end.
*)
  Definition mkPointstoVar x f e : expr typ func :=
     mkAp tyVal tyAsn 
          (mkAp tyString (tyArr tyVal tyAsn)
                (mkAp tyVal (tyArr tyString (tyArr tyVal tyAsn))
                      (mkPure (tyArr tyVal (tyArr tyString (tyArr tyVal tyAsn))) 
                               fPointsto)
                      (App (Inj fStackGet) (mkString x)))
                (mkPure tyString (mkString f)))
          e.
(*
  Definition test_lemma :=
    @lemmaD typ (expr typ func) RType_typ Expr_expr (expr typ func)
            (fun tus tvs e => exprD' tus tvs tyProp e)
            _
            nil nil.
*)
End JavaFunc.
