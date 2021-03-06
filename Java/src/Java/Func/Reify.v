Require Import MirrorCore.Reify.Reify.
Require Import MirrorCore.Lambda.Expr.

Require Import Java.Logic.AssertionLogic.
Require Import Java.Logic.SpecLogic.
Require Import Java.Language.Program.
Require Import Java.Language.Lang.
Require Import Java.Semantics.OperationalSemantics.
Require Import Java.Func.JavaFunc.
Require Import Java.Func.JavaType.

Require Import Charge.ModularFunc.ILogicFunc.
Require Import Charge.ModularFunc.BILogicFunc.
Require Import Charge.ModularFunc.LaterFunc.
Require Import Charge.ModularFunc.BaseFunc.
Require Import Charge.ModularFunc.ListFunc.
Require Import Charge.ModularFunc.OpenFunc.
Require Import Charge.ModularFunc.EmbedFunc.
Require Import Charge.Open.Stack.
Require Import Charge.Open.Subst.
Require Import Charge.Open.OpenILogic.
Require Import Charge.Logics.BILogic.
Require Import Charge.Logics.Later.

Require Import ExtLib.Structures.Applicative.

Reify Declare Patterns patterns_java_typ := typ.

Reify Declare Patterns patterns_java := (ExprCore.expr typ func).

Local Instance Applicative_Fun A : Applicative (Fun A) :=
{ pure := fun _ x _ => x
; ap := fun _ _ f x y => (f y) (x y)
}.

(*
Reify Declare Patterns const_for_cmd += ((RHasType cmd ?0) => (fun (c : id cmd) => mkCmd [c] : expr typ func)).
*)

Require Import MirrorCore.Reify.Reify.

Axiom t : Type.
Reify Declare Patterns t_pat := t.



Reify Declare Syntax t_cmd :=
{ (@Patterns.CPatterns t t_pat) }.


Reify Declare Syntax reify_imp_typ :=
  { 
  	(@Patterns.CPatterns typ patterns_java_typ)
  }.

Reify Declare Typed Table term_table : BinNums.positive => reify_imp_typ.

Check term_table.

Locate exprD.

Require Import MirrorCore.ExprI.

Check @exprD.
Print Expr.
Print RType.
Let Ext x := @ExprCore.Inj typ func (inl (inl (inl (inl (inl (inl (inl (inl x)))))))).

Reify Declare Syntax reify_imp :=
  { (@Patterns.CFirst _
  		((@Patterns.CVar _ (@ExprCore.Var typ func)) ::
  	     (@Patterns.CPatterns _ patterns_java) ::
         (@Patterns.CApp _ (@ExprCore.App typ func)) ::
    	 (@Patterns.CAbs _ reify_imp_typ (@ExprCore.Abs typ func)) ::
    	 (@Patterns.CTypedTable _ _ _ term_table Ext) :: nil))
  }.

Definition stack_get (x : Lang.var) (s : Lang.stack) := s x.

Notation "'ap_eq' '[' x ',' y ']'" :=
	 (ap (T := Fun Lang.stack) (ap (T := Fun Lang.stack) (pure (T := Fun Lang.stack) (@eq val)) x) y).
Notation "'ap_pointsto' '[' x ',' f ',' e ']'" := 
	(ap (T := Fun Lang.stack) (ap (T := Fun Lang.stack) (ap (T := Fun Lang.stack) 
		(pure (T := Fun Lang.stack) pointsto) (stack_get x)) 
			(pure (T := Fun Lang.stack) f)) e).
Notation "'ap_typeof' '[' e ',' C ']'" :=
	(ap (T := Fun Lang.stack) 
	    (ap (T := Fun Lang.stack) 
	        (pure (T := Fun Lang.stack) typeof) 
	        (pure (T := Fun Lang.stack) C))
	    e).
(*
Definition set_fold_fun (x f : String.string) (P : sasn) :=
	ap_pointsto [x, f, pure null] ** P.
*)
Let _Inj := @ExprCore.Inj typ func.

Require Import Java.Examples.ListModel.
(*
Reify Seed Typed Table term_table += 1 => [ (tyArr tyVal (tyArr (tyList tyVal) tyAsn)) , List ].
Reify Seed Typed Table term_table += 2 => [ (tyArr tyVal (tyArr (tyList tyVal) tyAsn)) , NodeList ].
*)

Local Notation "x @ y" := (@RApp x y) (only parsing, at level 30).
Local Notation "'!!' x" := (@RExact _ x) (only parsing, at level 25).
Local Notation "'?' n" := (@RGet n RIgnore) (only parsing, at level 25).
Local Notation "'?!' n" := (@RGet n RConst) (only parsing, at level 25).
Local Notation "'#'" := RIgnore (only parsing, at level 0).

Reify Pattern patterns_java_typ += (@RImpl (?0) (?1)) => (fun (a b : function reify_imp_typ) => tyArr a b).

Reify Pattern patterns_java_typ += (!! asn)  => tyAsn.
Reify Pattern patterns_java_typ += (!! sasn) => tySasn.
Reify Pattern patterns_java_typ += (!! (@vlogic Lang.var val)) => tyPure.
Reify Pattern patterns_java_typ += (!! Prop) => tyProp.
Reify Pattern patterns_java_typ += (!! spec) => tySpec.

Reify Pattern patterns_java_typ += (!! @prod @ ?0 @ ?1) => (fun (x y : function reify_imp_typ) => tyPair x y).
Reify Pattern patterns_java_typ += (!! (@list String.string)) => tyVarList.
Reify Pattern patterns_java_typ += (!! (@list field)) => tyFields.
Reify Pattern patterns_java_typ += (!! (@list (@Open.expr (Lang.var) val))) => tyVarList.
Reify Pattern patterns_java_typ += (!! (@list (Lang.var * @Open.expr (Lang.var) val))) => tySubstList.
Reify Pattern patterns_java_typ += (!! (@substlist Lang.var val)) => tySubstList.
Reify Pattern patterns_java_typ += (!! @list @ ?0) => (fun x : function reify_imp_typ => tyList x).
Reify Pattern patterns_java_typ += (!! nat) => tyNat.
Reify Pattern patterns_java_typ += (!! val) => tyVal.
Reify Pattern patterns_java_typ += (!! bool) => tyBool.
Reify Pattern patterns_java_typ += (!! field) => tyString.
Reify Pattern patterns_java_typ += (!! class) => tyString.
Reify Pattern patterns_java_typ += (!! @Open.open Lang.var val asn) => tySasn.
Reify Pattern patterns_java_typ += (!! @Open.open Lang.var val Prop) => tyPure.
Reify Pattern patterns_java_typ += (!! Lang.var) => tyString.
Reify Pattern patterns_java_typ += (!! String.string) => tyString.
Reify Pattern patterns_java_typ += (!! Program) => tyProg.
Reify Pattern patterns_java_typ += (!! Lang.stack) => tyStack.
Reify Pattern patterns_java_typ += (!! @Stack.stack Lang.var val) => tyStack.
Reify Pattern patterns_java_typ += (!! cmd) => tyCmd.
Reify Pattern patterns_java_typ += (!! dexpr) => tyExpr.
Reify Pattern patterns_java_typ += (!! (@Open.expr Lang.var val)) => tyExpr.
Reify Pattern patterns_java_typ += (!! @Subst.subst (String.string) val) => tySubst.

Reify Pattern patterns_java_typ += (!! Fun @ ?0 @ ?1) => (fun (a b : function reify_imp_typ) => tyArr a b).

Reify Pattern patterns_java += (RHasType String.string (?0)) => (fun (s : id String.string) => mkString (func := func) (typ := typ) s).
Reify Pattern patterns_java += (RHasType field (?0)) => (fun (f : id field) => mkString (func := func) f).
Reify Pattern patterns_java += (RHasType Lang.var (?0)) => (fun (f : id Lang.var) => mkString (func := func) f).
Reify Pattern patterns_java += (RHasType val (?0)) => (fun (v : id val) => mkVal v).
Reify Pattern patterns_java += (RHasType bool (?0)) => (fun (b : id bool) => mkBool (func := func) b).
Reify Pattern patterns_java += (RHasType nat (?0)) => (fun (n : id nat) => mkNat (func := func) n).
Reify Pattern patterns_java += (RHasType cmd (?0)) => (fun (c : id cmd) => mkCmd c).
Reify Pattern patterns_java += (RHasType dexpr (?0)) => (fun (e : id dexpr) => mkDExpr e).
Reify Pattern patterns_java += (RHasType Program (?0)) => (fun (P : id Program) => mkProg P).
Reify Pattern patterns_java += (RHasType (list field) (?0)) => (fun (fs : id (list field)) => mkFields fs).
Reify Pattern patterns_java += (RHasType class (?0)) => (fun (c : id class) => mkString (func := func) c).

Reify Pattern patterns_java += (RHasType (@list dexpr) (?0)) => (fun (es : id (@list dexpr)) => mkExprList es).
Reify Pattern patterns_java += (RHasType (@list String.string) (?0)) => (fun (vs : id (@list String.string)) => mkFields vs).
Reify Pattern patterns_java += (!! (@eq) @ ?0) => (fun (x : function reify_imp_typ) => fEq (func := expr typ func) x).

(** Intuitionistic Operators **)
Reify Pattern patterns_java += (!! @ILogic.lentails @ ?0 @ #) => (fun (x : function reify_imp_typ) => fEntails (func := expr typ func) x).
Reify Pattern patterns_java += (!! @ILogic.ltrue @ ?0 @ #) => (fun (x : function reify_imp_typ) => mkTrue (func := func) x).
Reify Pattern patterns_java += (!! @ILogic.lfalse @ ?0 @ #) => (fun (x : function reify_imp_typ) => mkFalse (func := func) x).

Reify Pattern patterns_java += (!! @ILogic.land @ ?0 @ #) => (fun (x : function reify_imp_typ) => fAnd (func := expr typ func) x).
Reify Pattern patterns_java += (!! @ILogic.lor @ ?0 @ #) => (fun (x : function reify_imp_typ) => fOr (func := expr typ func) x).
Reify Pattern patterns_java += (!! @ILogic.limpl @ ?0 @ #) => (fun (x : function reify_imp_typ) => fImpl (func := expr typ func) x).

Reify Pattern patterns_java += (!! @ILogic.lexists @ ?0 @ # @ ?1) => (fun (x y : function reify_imp_typ) => fExists (func := expr typ func) y x).

Reify Pattern patterns_java += (!! @ILogic.lforall @ ?0 @ # @ ?1) => (fun (x y : function reify_imp_typ) => fForall (func := expr typ func) y x).
(** Embedding Operators **)
Reify Pattern patterns_java += (!! @ILEmbed.embed @ ?0 @ ?1 @ #) => (fun (x y : function reify_imp_typ) => fEmbed (func := expr typ func) x y).

Reify Pattern patterns_java += (!! @pair @ ?0 @ ?1) => (fun (x y : function reify_imp_typ) => fPair (func := expr typ func) x y).

(** Special cases for Coq's primitives **)
Reify Pattern patterns_java += (!! True) => (mkTrue (func := func) tyProp).
Reify Pattern patterns_java += (!! False) => (mkFalse (func := func) tyProp).
Reify Pattern patterns_java += (!! and) => (fAnd (func := expr typ func) tyProp).

Reify Pattern patterns_java += (!! or) => (fOr (func := expr typ func) tyProp).

Reify Pattern patterns_java += (!! ex @ ?0) => (fun (x : function reify_imp_typ) => fExists (func := expr typ func) x tyProp).

Reify Pattern patterns_java += (RPi (?0) (?1)) => (fun (x : function reify_imp_typ) (y : function reify_imp) =>
                                                   ExprCore.App (fForall (func := expr typ func) x tyProp) (ExprCore.Abs x y)).

Reify Pattern patterns_java += (RImpl (?0) (?1)) => (fun (x y : function reify_imp) => 
	ExprCore.App (ExprCore.App (fImpl (func := expr typ func) tyProp) x) y).

(** Separation Logic Operators **)
Reify Pattern patterns_java += (!! @BILogic.sepSP @ ?0 @ #) => (fun (x : function reify_imp_typ) => (fStar (func := expr typ func) x)).
Reify Pattern patterns_java += (!! @BILogic.wandSP @ ?0 @ #) => (fun (x : function reify_imp_typ) => (fWand (func := expr typ func) x)).
Reify Pattern patterns_java += (!! @BILogic.empSP @ ?0 @ #) => (fun (x : function reify_imp_typ) => (mkEmp (func := func) x)).

Reify Pattern patterns_java += (!! @Later.illater @ ?0 @ #) => (fun (x : function reify_imp_typ) => (fLater (func := expr typ func) x)).

Reify Pattern patterns_java += (!! method_spec) => (fMethodSpec).

(** Program Logic **)


Reify Pattern patterns_java += (!! triple) => (fTriple).
Reify Pattern patterns_java += (!!method_lookup) => fMethodLookup.
Reify Pattern patterns_java += (!!field_lookup) => fFieldLookup.
Reify Pattern patterns_java += (!!m_ret) => fMethodRet.
Reify Pattern patterns_java += (!!m_body) => fMethodBody.
Reify Pattern patterns_java += (!!m_params) => fMethodArgs.

Reify Pattern patterns_java += (!! eval @ (RHasType dexpr (?0))) => (fun e : id dexpr => evalDExpr e).
Reify Pattern patterns_java += (!! stack_get) => (fStackGet (typ := typ) (func := expr typ func)).
Reify Pattern patterns_java += (!! stack_add (val := val)) => (fStackSet (typ := typ) (func := expr typ func)).

Reify Pattern patterns_java += (!! pointsto) => (fPointsto).
Reify Pattern patterns_java += (!! prog_eq) => (fProgEq).
Reify Pattern patterns_java += (!! typeof) => (fTypeOf).

Reify Pattern patterns_java += (!! (@substl_trunc Lang.var val _)) => (fTruncSubst (func := expr typ func) (typ := typ)).
Reify Pattern patterns_java += (!! (@substl Lang.var val _)) => (fSubst (func := expr typ func) (typ := typ)).

Reify Pattern patterns_java += (!! @nil @ ?0) => (fun (x : function reify_imp_typ) => (fNil (func := expr typ func) x)).
Reify Pattern patterns_java += (!! @cons @ ?0) => (fun (x : function reify_imp_typ) => (fCons (func := expr typ func) x)).
Reify Pattern patterns_java += (!! @length @ ?0) => (fun (x : function reify_imp_typ) => (fLength (func := expr typ func) x)).
Reify Pattern patterns_java += (!! @zip @ ?0 @ ?1) => (fun (x y : function reify_imp_typ) => (fZip (func := expr typ func) x y)).
Reify Pattern patterns_java += (!! @map @ ?0 @ ?1) => (fun (x y : function reify_imp_typ) => (fMap (func := expr typ func) x y)).
Reify Pattern patterns_java += (!! @fold_right @ ?0 @ ?1) => (fun (x y : function reify_imp_typ) => (fFold (func := expr typ func) x y)).

Reify Pattern patterns_java += (!! (@apply_subst Lang.var val) @ ?0) => (fun (x : function reify_imp_typ) => fApplySubst (func := expr typ func) x).
Reify Pattern patterns_java += (!! @subst1 Lang.var val _) => (fSingleSubst (func := expr typ func)).
Reify Pattern patterns_java += (!! @field_lookup) => (fFieldLookup).
(** Applicative **)
Reify Pattern patterns_java += (!! @Applicative.ap @ !! (Fun Lang.stack) @ # @ ?0 @ ?1) => (fun (x y : function reify_imp_typ) => fAp (func := expr typ func) x y).
Reify Pattern patterns_java += (!! @Applicative.pure @ !! (Fun Lang.stack) @ # @ ?0) => (fun (x : function reify_imp_typ) => fConst (func := expr typ func) x).

Let elem_ctor : forall x : typ, typD x -> @SymEnv.function _ _ :=
  @SymEnv.F _ _.

Ltac reify_imp e :=
  let k fs e :=
      pose e in
  reify_expr reify_imp k
             [ (fun (y : @mk_dvar_map _ _ _ _ term_table elem_ctor) => True) ]
             [ e ].

Require Import ILogic.

Goal (forall (Pr : Program) (C : class) (v : val) (fields : list field), True).
  intros Pr C v fields.
  reify_imp (typeof C v).

  reify_imp (field_lookup).
  reify_imp (field_lookup Pr C fields).

  pose ((fun (_ : @Stack.stack Lang.var val) => null) : @Open.expr Lang.var val) as e2.
  pose ((fun (_ : Lang.stack) => null) : Lang.stack -> val) as e3.


  reify_imp (pure (T := Fun Lang.stack) pointsto).

  reify_imp (fun a b c => pointsto a b c).

  reify_imp e2.
  
  reify_imp e3.

  reify_imp (ap (T := Fun Lang.stack) (ap (T := Fun Lang.stack) (pure (@eq val)) e2) e2).

  pose (E_val (vint 3)) as d.

  reify_imp ((ap (ap (T := Fun Lang.stack) (pure (@eq val)) (eval d)) (pure (vbool true)))).
  
  generalize String.EmptyString. intro c.
   reify_imp (ltrue |-- {[ ltrue ]} cread c c c {[ ltrue ]}).

  reify_imp cskip.

  reify_imp (forall P, P /\ P).

  reify_imp (forall x : nat, x = x).
  reify_imp (exists x : nat, x = x).
  reify_imp (@map nat nat).
  reify_imp (@subst1 Lang.var val _).
  reify_imp (cseq cskip cskip).
  
  reify_imp (ILogic.lentails True True).

  reify_imp ((True -> False) -> True).
  reify_imp (forall P Q, P /\ Q).
  reify_imp (forall P : sasn, ILogic.lentails ILogic.ltrue P).
  reify_imp (forall (G : spec) (P Q : sasn), ILogic.lentails G (triple P Q cskip)).
  generalize (String.EmptyString : String.string).
  intro x.

  reify_imp stack_get.

  reify_imp (stack_get x).

  reify_imp (x = x).

  reify_imp (@ltrue sasn _).
  exact I.

Defined.

Ltac reify_aux e n :=
  let k fs e :=
      pose e as n in
  reify_expr reify_imp k
             [ (fun (y : @mk_dvar_map _ _ _ _ term_table elem_ctor) => True) ]
             [ e ].
