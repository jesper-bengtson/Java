Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Data.String.
Require Import ExtLib.Data.Sum.
Require Import ExtLib.Data.Positive.
Require Import ExtLib.Tactics.Consider.

Require Import ChargeCore.Open.Subst.
Require Import ChargeCore.Open.Open.
Require Import ChargeCore.Open.Stack.
Require Import ChargeCore.Logics.BILogic.
Require Import Charge.Views.ILogicView.
Require Import Charge.Views.BILogicView.
Require Import Charge.Views.SubstView.
Require Import Charge.Views.EmbedView.
Require Import Java.Func.ListOpView.

Require Import MirrorCore.TypesI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.Lemma.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Views.ViewSumN.
Require Import MirrorCore.Views.FuncView.
Require Import MirrorCore.syms.SymEnv.
Require Import MirrorCore.syms.SymSum.
Require Import MirrorCore.syms.SymOneOf.
Require Import MirrorCore.Subst.FMapSubst.
Require Import MirrorCore.Views.ListView.
Require Import MirrorCore.Views.ProdView.
Require Import MirrorCore.Views.EqView.
Require Import MirrorCore.Views.ApplicativeView.
Require Import MirrorCore.Views.NatView.
Require Import MirrorCore.Views.BoolView.
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
{ rel_dec a b := match java_func_eq a b with
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
  match bf as bf return match typeof_java_func bf return Type@{Urefl} with
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
{ typeof_sym := typeof_java_func;
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

Inductive list' :=
| nil' : list'
| cons' : OneOfType.TypeR -> list' -> list'.

Fixpoint list_to_pmap_aux (lst : list') (p : positive)
: OneOfType.pmap :=
  match lst with
  | nil' => OneOfType.Empty
  | cons' x xs => OneOfType.pmap_insert p (list_to_pmap_aux xs (p + 1)) x
  end.

Definition list_to_pmap (lst : list') := list_to_pmap_aux lst 1.


Set Printing Universes.

Definition func_map : OneOfType.pmap :=
	list_to_pmap
	  (cons' java_func
          (cons' SymEnv.func
          (cons' (@ilfunc typ)
          (cons' (@bilfunc typ)
          (cons' (@list_func typ)
	  (cons' (@subst_func typ)
          (cons' (@embed_func typ)
          (cons' (natFunc:Type)
          (cons' (stringFunc:Type)
          (cons' (boolFunc:Type)
          (cons' (@prod_func typ)
          (cons' (@eq_func typ)
          (cons' (@ap_func typ)
          (cons' (@listOp_func typ) nil')))))))))))))).

Definition func := OneOfType.OneOf func_map.

Check @red_fold typ func.

Global Instance JavaView_func : FuncView func java_func :=
  FuncViewPMap 1 func_map eq_refl.
Global Instance ILogicView_func : FuncView func (@ilfunc typ) :=
  FuncViewPMap 3 func_map eq_refl.
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
Global Instance BoolView_func : FuncView func boolFunc :=
  FuncViewPMap 10 func_map eq_refl.
Global Instance ProdView_func : FuncView func (@prod_func typ) :=
  FuncViewPMap 11 func_map eq_refl.
Global Instance Eq_func : FuncView func (@eq_func typ) :=
  FuncViewPMap 12 func_map eq_refl.
Global Instance ApplicativeView_func : FuncView func (@ap_func typ) :=
  FuncViewPMap 13 func_map eq_refl.
Global Instance ListOp_func : FuncView func (@listOp_func typ) :=
  FuncViewPMap 14 func_map eq_refl.

Section MakeJavaFunc.

  Definition fVal v : func:= f_insert (pVal v).
  Definition fProg P : func:= f_insert (pProg P).
  Definition fMethod M : func:= f_insert (pMethod M).
  Definition fCmd c : func:= f_insert (pCmd c).
  Definition fDExpr e : func:= f_insert (pExpr e).
  Definition fFields f : func:= f_insert (pFields f).

  Definition fMethodSpec : func:= f_insert pMethodSpec.
  Definition fProgEq : func:= f_insert pProgEq.
  Definition fTriple : func:= f_insert pTriple.
  Definition fTypeOf : func:= f_insert pTypeOf.
  Definition fFieldLookup : func:= f_insert pFieldLookup.
  Definition fMethodLookup : func:= f_insert pMethodLookup.
  Definition fPointsto : func:= f_insert pPointsto.
  Definition fNull : func:= f_insert pNull.

  Definition fMethodBody : func:= f_insert pMethodBody.
  Definition fMethodArgs : func:= f_insert pMethodArgs.
  Definition fMethodRet : func:= f_insert pMethodRet.

  Definition fPlusE : func:= f_insert pPlus.
  Definition fMinusE : func:= f_insert pMinus.
  Definition fTimesE : func:= f_insert pTimes.
  Definition fAndE : func:= f_insert pAnd.
  Definition fOrE : func:= f_insert pOr.
  Definition fNotE : func:= f_insert pNot.
  Definition fLtE : func:= f_insert pLt.
  Definition fValEq : func:= f_insert pValEq.

Require Import MirrorCore.Views.Ptrns.
Require Import MirrorCore.Lambda.Ptrns.

  Definition fptrnVal {T : Type} (p : Ptrns.ptrn val T) : ptrn java_func T :=
    fun f U good bad =>
      match f with
        | pVal v => p v U good (fun x => bad f)
        | _ => bad f
      end.

  Definition fptrnProg {T : Type} (p : Ptrns.ptrn Program T) : ptrn java_func T :=
    fun f U good bad =>
      match f with
        | pProg P => p P U good (fun x => bad f)
        | _ => bad f
      end.

  Definition fptrnMethod {T : Type} (p : Ptrns.ptrn Method T) : ptrn java_func T :=
    fun f U good bad =>
      match f with
        | pMethod M => p M U good (fun x => bad f)
        | _ => bad f
      end.

  Definition fptrnCmd {T : Type} (p : Ptrns.ptrn cmd T) : ptrn java_func T :=
    fun f U good bad =>
      match f with
        | pCmd c => p c U good (fun x => bad f)
        | _ => bad f
      end.

  Definition fptrnExpr {T : Type} (p : Ptrns.ptrn dexpr T) : ptrn java_func T :=
    fun f U good bad =>
      match f with
        | pExpr e => p e U good (fun x => bad f)
        | _ => bad f
      end.

  Definition fptrnFields {T : Type} (p : Ptrns.ptrn (list string) T) : ptrn java_func T :=
    fun f U good bad =>
      match f with
        | pFields fs => p fs U good (fun x => bad f)
        | _ => bad f
      end.

  Definition fptrnMethodSpec : ptrn java_func unit :=
    fun f U good bad =>
      match f with
        | pMethodSpec => good tt
        | _ => bad f
      end.

  Definition fptrnProgEq : ptrn java_func unit :=
    fun f U good bad =>
      match f with
        | pProgEq => good tt
        | _ => bad f
      end.

  Definition fptrnTriple : ptrn java_func unit :=
    fun f U good bad =>
      match f with
        | pTriple => good tt
        | _ => bad f
      end.

  Definition fptrnPointsto : ptrn java_func unit :=
    fun f U good bad =>
      match f with
        | pPointsto => good tt
        | _ => bad f
      end.

  Definition fptrnNull : ptrn java_func unit :=
    fun f U good bad =>
      match f with
        | pNull => good tt
        | _ => bad f
      end.

  Definition fptrnMethodBody : ptrn java_func unit :=
    fun f U good bad =>
      match f with
        | pMethodBody => good tt
        | _ => bad f
      end.

  Definition fptrnMethodArgs : ptrn java_func unit :=
    fun f U good bad =>
      match f with
        | pMethodArgs => good tt
        | _ => bad f
      end.

  Definition fptrnMethodRet : ptrn java_func unit :=
    fun f U good bad =>
      match f with
        | pMethodRet => good tt
        | _ => bad f
      end.

  Definition fptrnPlus : ptrn java_func unit :=
    fun f U good bad =>
      match f with
        | pPlus => good tt
        | _ => bad f
      end.

  Definition fptrnMinus : ptrn java_func unit :=
    fun f U good bad =>
      match f with
        | pMinus => good tt
        | _ => bad f
      end.

  Definition fptrnTimes : ptrn java_func unit :=
    fun f U good bad =>
      match f with
        | pTimes => good tt
        | _ => bad f
      end.

  Definition fptrnAndE : ptrn java_func unit :=
    fun f U good bad =>
      match f with
        | pAnd => good tt
        | _ => bad f
      end.

  Definition fptrnOrE : ptrn java_func unit :=
    fun f U good bad =>
      match f with
        | pOr => good tt
        | _ => bad f
      end.

  Definition fptrnNotE : ptrn java_func unit :=
    fun f U good bad =>
      match f with
        | pNot => good tt
        | _ => bad f
      end.

  Definition fptrnLtE : ptrn java_func unit :=
    fun f U good bad =>
      match f with
        | pMethodSpec => good tt
        | _ => bad f
      end.

  Definition fptrnValEqE : ptrn java_func unit :=
    fun f U good bad =>
      match f with
        | pMethodSpec => good tt
        | _ => bad f
      end.

  Definition fptrnFieldLookup : ptrn java_func unit :=
    fun f U good bad =>
      match f with
        | pFieldLookup => good tt
        | _ => bad f
      end.

  Definition ptrnTriple {A B C : Type}
             (a : ptrn (expr typ func) A)
             (b : ptrn (expr typ func) B)
             (c : ptrn (expr typ func) C) : ptrn (expr typ func) (A * B * C) :=
    pmap (fun a_b_c => let '(_, a, b, c) := a_b_c in (a, b, c))
         (app (app (app (inj (ptrn_view _ fptrnTriple)) a) b) c).

  Definition mkTriple P c Q : expr typ func := App (App (App (Inj fTriple) P) Q) c.
  Definition mkFieldLookup P C f : expr typ func := App (App (App (Inj fFieldLookup) P) C) f.
  Definition mkTypeOf C x : expr typ func := App (App (Inj fTypeOf) C) x.
  Definition mkProgEq P : expr typ func := App (Inj fProgEq) P.

  Definition mkMethodBody (M : Method) : expr typ func :=
    App (Inj fMethodBody) (Inj (fMethod M)).
  Definition mkMethodArgs (M : Method) : expr typ func :=
    App (Inj fMethodArgs) (Inj (fMethod M)).
  Definition mkMethodRet (M : Method) : expr typ func :=
    App (Inj fMethodRet) (Inj (fMethod M)).


  Definition mkExprList es :=
    (fold_right (fun (e : dexpr) (acc : expr typ func) =>
		   mkCons tyExpr (Inj (fDExpr e)) acc) (mkNil tyExpr) es).

Fixpoint evalDExpr (e : dexpr) : expr typ func :=
    match e with
    | E_val v => mkPure tyVal (Inj (fVal v))
    | E_var x => App (Inj fStackGet) (mkString x)
    | E_plus e1 e2 => mkAps (Inj fPlusE) ((evalDExpr e2, tyVal)::(evalDExpr e1, tyVal)::nil) tyVal
    | E_minus e1 e2 => mkAps (Inj fMinusE) ((evalDExpr e2, tyVal)::(evalDExpr e1, tyVal)::nil) tyVal
    | E_times e1 e2 => mkAps (Inj fTimesE) ((evalDExpr e2, tyVal)::(evalDExpr e1, tyVal)::nil) tyVal
    | E_and e1 e2 => mkAps (Inj fAndE) ((evalDExpr e2, tyVal)::(evalDExpr e1, tyVal)::nil) tyVal
    | E_or e1 e2 => mkAps (Inj fOrE) ((evalDExpr e2, tyVal)::(evalDExpr e1, tyVal)::nil) tyVal
    | E_not e => mkAps (Inj fNotE) ((evalDExpr e, tyVal)::nil) tyVal
    | E_lt e1 e2 => mkAps (Inj fLtE) ((evalDExpr e2, tyVal)::(evalDExpr e1, tyVal)::nil) tyVal
    | E_eq e1 e2 => mkAps (Inj fValEq) ((evalDExpr e2, tyVal)::(evalDExpr e1, tyVal)::nil) tyVal
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

  Require Import ExtLib.Structures.Applicative.

  Local Instance Applicative_Fun A : Applicative (Fun A) :=
    { pure := fun _ x _ => x
      ; ap := fun _ _ f x y => (f y) (x y)
    }.

  Import OneOfType.

  Definition RSym_sub_func (p : positive) :
    RSym (match pmap_lookup' func_map p with
          | _Some T => T
          | _None => Empty_set
          end).
  Proof.
    destruct p; simpl; [| | apply _].
    destruct p; simpl; [| | apply _].
    destruct p; simpl; [| | apply _].
    induction p; simpl; intuition; apply RSym_Empty_set.
    destruct p; simpl; [| | apply _].
    induction p; simpl; intuition; apply RSym_Empty_set.
    induction p; simpl; intuition; apply RSym_Empty_set.
    destruct p; simpl; [| | apply _].
    destruct p; simpl; [| | apply (RSym_ApFunc (T := (Fun stack)))].
    induction p; simpl; intuition; apply RSym_Empty_set.
    induction p; simpl; intuition; apply RSym_Empty_set.
    destruct p; simpl; [| | apply _].
    induction p; simpl; intuition; apply RSym_Empty_set.
    induction p; simpl; intuition; apply RSym_Empty_set.
    destruct p; simpl; [| | apply RSym_func; apply fs].
    destruct p; simpl; [| | apply RSym_SubstFunc].
    destruct p; simpl; [| | apply _].
    induction p; simpl; intuition; apply RSym_Empty_set.
    induction p; simpl; intuition; apply RSym_Empty_set.
    destruct p; simpl; [| | apply _].
    induction p; simpl; intuition; apply RSym_Empty_set.
    induction p; simpl; intuition; apply RSym_Empty_set.
    destruct p; simpl; [| | apply _].
    destruct p; simpl; [| | apply _].
    induction p; simpl; intuition; apply RSym_Empty_set.
    induction p; simpl; intuition; apply RSym_Empty_set.
    destruct p; simpl; [| | apply _].
    induction p; simpl; intuition; apply RSym_Empty_set.
    induction p; simpl; intuition; apply RSym_Empty_set.
  Defined.

  Instance RSymOk_Empty_set : RSymOk RSym_Empty_set :=
    {
      sym_eqbOk a b :=
        match a with
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
    destruct p; simpl; [| | apply _].
    induction p; simpl; intuition; apply RSymOk_Empty_set.
    induction p; simpl; intuition; apply RSymOk_Empty_set.
    destruct p; simpl; [| | apply _].
    induction p; simpl; intuition; apply RSymOk_Empty_set.
    induction p; simpl; intuition; apply RSymOk_Empty_set.
    destruct p; simpl; [| | apply _].
    destruct p; simpl; [| | apply _].
    destruct p; simpl; [| | apply _].
    induction p; simpl; intuition; apply RSymOk_Empty_set.
    induction p; simpl; intuition; apply RSymOk_Empty_set.
    destruct p; simpl; [| | apply _].
    induction p; simpl; intuition; apply RSymOk_Empty_set.
    induction p; simpl; intuition; apply RSymOk_Empty_set.
    destruct p; simpl; [| | apply _].
    destruct p; simpl; [| | apply _].
    induction p; simpl; intuition; apply RSymOk_Empty_set.
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
Check SubstI.SubstOk.
  Global Instance SO : @SubstI.SubstOk _ _ _ _ _ SS :=
    @FMapSubst.SUBST.SubstOk_subst typ RType_typ (expr typ func) _.
  Global Instance SUO : @SubstI.SubstUpdateOk _ _ _ _ _ _ SU SO :=  @FMapSubst.SUBST.SubstUpdateOk_subst typ RType_typ (expr typ func) _ _.
(*
  Global Instance MA : MentionsAny (expr typ func) := {
    mentionsAny := ExprCore.mentionsAny
  }.

  Global Instance MAOk : MentionsAnyOk MA _ _.
  Proof.
    admit.
  Qed.
*)

Definition ptrnPair {A B T U : Type} (t : ptrn A T) (u : ptrn B U) : 
  ptrn (A * B) (T * U) :=
  fun e C good bad =>
    Mbind (Mrebuild (fun x : A => (x, snd e)) (t (fst e)))
          (fun x : T => Mmap (fun y : U => (x, y)) (Mrebuild (pair (fst e)) (u (snd e)))) good bad.

Definition ptrn_tyArr (T U : Type) (t : ptrn typ T) (u : ptrn typ U) : ptrn typ (T * U) :=
  fun e A good bad =>
    match e with
    | tyArr a b => 
      Mbind (Mrebuild (fun x : typ => tyArr x b) (t a))
            (fun x : T => Mmap (fun y : U => (x, y)) (Mrebuild (tyArr a) (u b))) good bad
    | _ => bad e
    end.
      
Definition ptrn_tyProp : ptrn typ unit :=
  fun t T good bad =>
    match t with
      | tyProp => good tt
      | _ => bad t
    end.

Definition ptrn_tyAsn : ptrn typ unit :=
  fun t T good bad =>
    match t with
      | tyAsn => good tt
      | _ => bad t
    end.

Definition ptrn_tyVal : ptrn typ unit :=
  fun t T good bad =>
    match t with
      | tyVal => good tt
      | _ => bad t
    end.

Definition ptrn_tyString : ptrn typ unit :=
  fun t T good bad =>
    match t with
      | tyString => good tt
      | _ => bad t
    end.

Definition ptrn_tyStack : ptrn typ unit := 
  fun t T good bad =>
    match t with
      | tyStack => good tt
      | _ => bad t
    end.

Definition ptrn_tyPure : ptrn typ unit := 
  fun t T good bad =>
    match t with
      | tyPure => good tt
      | _ => bad t
    end.

Definition ptrn_tySasn : ptrn typ unit := 
  fun t T good bad =>
    match t with
      | tySasn => good tt
      | _ => bad t
    end.

Definition ptrnApEq {T A B : Type} (t : ptrn typ T) 
      (a : ptrn (expr typ func) A) (b : ptrn (expr typ func) B) : ptrn (expr typ func) (T * A * B) :=
  Ptrns.pmap (fun x => (fst (fst (fst x)), snd (snd (fst x)), snd x))
             (ptrnAp (ptrnPair t ptrn_tyProp)
                     (ptrnAp (ptrnPair t (ptrn_tyArr t ptrn_tyProp))
                             (ptrnPure (ptrn_tyArr t (ptrn_tyArr t ptrn_tyProp)) (inj (ptrn_view _ (fptrnEq t))))
                             a) b).

Definition isEq : expr typ func -> bool :=
  run_ptrn
       (Ptrns.pmap (fun _ => true) 
                   (ptrnEmbed (ptrnPair ptrn_tyPure ptrn_tySasn) 
                              (ptrnApEq ptrn_tyVal ignore ignore))) false.



  Lemma evalDExpr_wt (e : dexpr) :
	  typeof_expr nil nil (evalDExpr e) = Some tyExpr.
  Proof.
    induction e.
    + simpl; reflexivity.
    + simpl; reflexivity.
    + simpl; rewrite IHe1, IHe2; reflexivity.
    + simpl; rewrite IHe1, IHe2; reflexivity.
    + simpl; rewrite IHe1, IHe2; reflexivity.
    + simpl; rewrite IHe1, IHe2; reflexivity.
    + simpl; rewrite IHe1, IHe2; reflexivity.
    + simpl; rewrite IHe; reflexivity.
    + simpl; rewrite IHe1, IHe2; reflexivity.
    + simpl; rewrite IHe1, IHe2; reflexivity.
  Qed.

  Definition is_pure : expr typ func -> bool :=
    run_ptrn
         (por (Ptrns.pmap (fun _ => true) (por (ptrnTrue ignore) (ptrnFalse ignore)))
              (Ptrns.pmap (fun x =>
                       match x with
                       | (tyPure, tySasn, tt) => true
                       | _ => false
                       end)
                    (ptrnEmbed get ignore)))
         false.

Require Import Charge.Tactics.BILNormalize.

(*
  Definition is_equality : expr typ func -> bool :=
    run_tptrn 
      (pdefault 
         (ptrnEmbed get get
         false)).
*)

  Definition mkPointstoVar x f e : expr typ func :=
     mkAp tyVal tyAsn
          (mkAp tyString (tyArr tyVal tyAsn)
                (mkAp tyVal (tyArr tyString (tyArr tyVal tyAsn))
                      (ApplicativeView.mkPure (tyArr tyVal (tyArr tyString (tyArr tyVal tyAsn)))
                               (Inj fPointsto))
                      (App (Inj fStackGet) (mkString x)))
                (ApplicativeView.mkPure tyString (mkString f)))
          e.
(*
  Definition test_lemma :=
    @lemmaD typ (expr typ func) RType_typ Expr_expr (expr typ func)
            (fun tus tvs e => exprD' tus tvs tyProp e)
            _
            nil nil.
*)
End JavaFunc.
