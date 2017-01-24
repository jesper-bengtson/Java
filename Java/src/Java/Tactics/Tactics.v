Require Import MirrorCore.Reify.Reify.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.AbsAppI.
Require Import MirrorCore.RTac.RTac.
Require Import MirrorCore.Subst.FMapSubst.
Require Import MirrorCore.syms.SymOneOf.
Require Import MirrorCore.Views.FuncView.
Require Import MirrorCore.Views.View.

Require Import Java.Func.JavaFunc.
Require Import Java.Func.Type.

Require Import Charge.Views.ILogicView.
Require Import Charge.Views.BILogicView.
Require Import Charge.Views.EmbedView.
Require Import Charge.Views.SubstView.
Require Import Charge.Patterns.ILogicPattern.
Require Import Charge.Patterns.BILogicPattern.
Require Import Charge.Patterns.EmbedPattern.
(*Require Import Charge.ModularFunc.LaterFunc.*)
Require Import MirrorCore.Lib.NatView.
Require Import MirrorCore.Lib.StringView.
Require Import MirrorCore.Lib.BoolView.
Require Import MirrorCore.Lib.ListView.
Require Import MirrorCore.Lib.ProdView.
Require Import MirrorCore.Lambda.ExprDsimul.
Require Import MirrorCore.CTypes.BaseType.
Require Import MirrorCore.CTypes.GenericTypes.
Require Import MirrorCore.Lib.ListOpView.

Require Import ChargeCore.Open.Stack.
Require Import ChargeCore.Open.Subst.
Require Import ChargeCore.Open.OpenILogic.

Require Import ChargeCore.Logics.BILogic.
(*Require Import Charge.Logics.Later.*)

Require Import Java.Logic.AssertionLogic.
Require Import Java.Logic.SpecLogic.
Require Import Java.Language.Program.
Require Import Java.Language.Lang.
Require Import Java.Semantics.OperationalSemantics.

Require Import ExtLib.Structures.Applicative.
Require Import ExtLib.Tactics.

Require Import Coq.PArith.BinPos.

Section Tactics.
  Context {fs : Environment}.

Program Definition exprD_Prop (uvar_env var_env : env) (e : expr typ func) :=
  let (tus, us) := split_env uvar_env in
  let (tvs, vs) := split_env var_env in
  match @exprD typ _ (expr typ func) _ tus tvs tyProp e with
    | Some e' => e' us vs
    | None => True
  end.

Definition goalD_Prop (uvar_env var_env : env) goal :=
  let (tus, us) := split_env uvar_env in
  let (tvs, vs) := split_env var_env in
  match goalD tus tvs goal with
    | Some e => e us vs
    | None => False
  end.

Definition goalD_aux tus tvs goal (us : HList.hlist typD tus) (vs : HList.hlist typD tvs) :=
  match goalD tus tvs goal with
    | Some e => Some (e us vs)
    | None => None
  end.
Check runOnGoals.
Definition run_tac tac goal :=
  runOnGoals tac (CTop nil nil) 
    (ctx_empty (typ := typ) (expr := expr typ func)) goal.

Lemma run_rtac_More tac s goal e
  (Hsound : rtac_sound tac) 
  (Hres : run_tac tac (GGoal e) = More_ s goal) :
  goalD_Prop nil nil goal -> exprD_Prop nil nil e.
Proof.
  intros He'.
  apply runOnGoals_sound_ind with (g := GGoal e) (ctx := CTop nil nil) 
  	(s0 := TopSubst (expr typ func) nil nil) in Hsound.
  unfold rtac_spec in Hsound. simpl in Hsound.
  unfold run_tac in Hres. simpl in Hres.
  rewrite Hres in Hsound.
  assert (WellFormed_Goal nil nil (GGoal (typ := typ) e)) as H1 by constructor.
  assert (WellFormed_ctx_subst (TopSubst (expr typ func) nil (@nil typ))) as H2 by constructor.
  specialize (Hsound H1 H2).
  destruct Hsound as [ Hwfs [ Hwfg Hsound ] ].
(*
  unfold Ctx.propD, exprD'_typ0 in Hsound.
  simpl in Hsound. unfold exprD_Prop, exprD; simpl.
  forward; inv_all; subst.

  destruct Hsound.
  inversion Hwfs; subst.
  simpl in H0; inv_all; subst.
  unfold pctxD in H0; inv_all; subst.
  apply H5.
  unfold goalD_Prop in He'. simpl in He'. forward; inv_all; subst.
  Unshelve. repeat decide equality. admit.*)
Admitted.

Lemma run_rtac_Solved tac s e
  (Hsound : rtac_sound tac) 
  (Hres : run_tac tac (GGoal e) = Solved s) :
  exprD_Prop nil nil e.
Proof.
  unfold run_tac in Hres.
  unfold rtac_sound in Hsound.
  assert (WellFormed_Goal nil nil (GGoal (typ := typ) e)) as H1 by constructor.
  assert (WellFormed_ctx_subst (TopSubst (expr typ func) nil (@nil typ))) as H2 by constructor.
  specialize (Hsound _ _ _ _ Hres H1 H2).
  destruct Hsound as [Hwfs Hsound].
  simpl in Hsound.
(*
  unfold Ctx.propD, exprD'_typ0 in Hsound.
  unfold exprD_Prop.
  simpl in Hsound. unfold exprD. simpl. forward.
  destruct Hsound. 
  SearchAbout pctxD.
  inversion Hwfs; subst. simpl in H8. inv_all; subst.
  admit.*)
Admitted.

End Tactics.

Definition my_exprD' := @exprD typ RType_typ (expr typ func).

Locate TSym_list_typ.
Print MirrorCore.CTypes.BaseType.
Locate funcD.

Print Transparent Dependencies TSym_base_typ.

Ltac cbv_denote :=
  cbv [
      MirrorCore.syms.SymEnv.funcD
      MirrorCore.syms.SymEnv.RSym_func

      (* ExtLib.Data.Option *)

        ExtLib.Data.Option.Applicative_option
        ExtLib.Data.Option.eq_option_eq
        ExtLib.Data.Option.Injective_Some

      (* MirrorCore.Util.Quant *)
      
        MirrorCore.Util.Quant._impls 
        MirrorCore.Util.Quant._and
        MirrorCore.Util.Quant._foralls 
        MirrorCore.Util.Quant._exists 
 
      (* MirrorCore.OpenT *)
        
        MirrorCore.OpenT.OpenT
        MirrorCore.OpenT.Applicative_OpenT
        MirrorCore.OpenT.Functor_OpenT
        MirrorCore.OpenT.OpenT_Use
        MirrorCore.OpenT.OpenTrel
        MirrorCore.OpenT.OpenTeq
        MirrorCore.OpenT.Open_Abs
        MirrorCore.OpenT.Open_App

      (* MirrorCore.CTypes.CoreTypes *)

        MirrorCore.CTypes.CoreTypes.TypeView_sym0
        MirrorCore.CTypes.CoreTypes.TypeViewOk_sym0

      (* MirrorCore.CTypes.GenericTypes *)

        MirrorCore.CTypes.GenericTypes.symD

      (* MirrorCore.CTypes.BaseType *)

         MirrorCore.CTypes.BaseType.base_typ_rect
         MirrorCore.CTypes.BaseType.base_typ_rec
         MirrorCore.CTypes.BaseType.base_typ_ind
         MirrorCore.CTypes.BaseType.base_typ_dec
         MirrorCore.CTypes.BaseType.base_typD
         MirrorCore.CTypes.BaseType.prop_match
         MirrorCore.CTypes.BaseType.string_match
         MirrorCore.CTypes.BaseType.TSym_base_typ
         MirrorCore.CTypes.BaseType.tyProp
         MirrorCore.CTypes.BaseType.tyNat
         MirrorCore.CTypes.BaseType.tyBool
         MirrorCore.CTypes.BaseType.tyString

      (* MirrorCore.CTypes.List *)

         MirrorCore.CTypes.ListType.list_typ_rect
         MirrorCore.CTypes.ListType.list_typ_rec
         MirrorCore.CTypes.ListType.list_typ_ind
         MirrorCore.CTypes.ListType.list_typ_dec
         MirrorCore.CTypes.ListType.list_typD
         MirrorCore.CTypes.ListType.TSym_list_typ
         MirrorCore.CTypes.ListType.tyList

      (* MirrorCore.CTypes.Prod *)

         MirrorCore.CTypes.ProdType.prod_typ_rect
         MirrorCore.CTypes.ProdType.prod_typ_rec
         MirrorCore.CTypes.ProdType.prod_typ_ind
         MirrorCore.CTypes.ProdType.prod_typ_dec
         MirrorCore.CTypes.ProdType.prod_typD
         MirrorCore.CTypes.ProdType.TSym_prod_typ
         MirrorCore.CTypes.ProdType.tyProd

      (* MirrorCore.Views.View *)

         MirrorCore.Views.View.f_view
         MirrorCore.Views.View.pv_ok
         MirrorCore.Views.View.PartialView_trans
         MirrorCore.Views.View.PartialView_transOk

        Option.Applicative_option List.Traversable_list
        app amap_substD
        map
        MirrorCore.EnvI.tenv
(*        ExtLib.Structures.Applicative.pure*)
        ExtLib.Structures.Traversable.mapT
        ExtLib.Data.List.mapT_list
        Coq.Init.Wf.well_founded
        goalD_aux
        
	(* ExprD' *)
        exprD symAs typeof_sym typeof_expr type_cast
        MirrorCore.Lambda.ExprDsimul.ExprDenote.lambda_exprD
        lambda_exprD
        lambda_exprD_simul func_simul
        Expr.Expr_expr
        (* RSym *)
        
        SymSum.RSym_sum Rcast Relim Rsym eq_sym MirrorCore.SymI.symD(* RSym_env*)
        Rcast_val eq_rect_r eq_rect Datatypes.id
        RSym_Empty RSymOneOf typeof_sym_OneOf symD_OneOf sym_eqb_OneOf
        (* Monad *)
        
        Monad.bind Monad.ret
        
        OptionMonad.Monad_option
        
        (* HList *)
        
        HList.hlist_hd HList.hlist_tl
        
        (* TypesI *)
        MirrorCore.TypesI.Rty
        TypesI.Typ1_App
        TypesI.Typ2_App
        TypesI.typD 
        TypesI.RFun 
        typ2_match typ2 typ2_cast
        typ1_match typ1 typ1_cast
        typ0_match typ0 typ0_cast
        castR castD
        (* ExprI *)
        
        MirrorCore.VariablesI.Var ExprVariables.ExprVar_expr
        MirrorCore.VariablesI.UVar
        MirrorCore.Lambda.ExprVariables.ExprUVar_expr
        ExprI.exprT_Inj ExprI.exprT_UseV ExprI.exprT_UseU
        exprT_App ExprI.exprT
        HList.nth_error_get_hlist_nth 
        
        exprT_GetVAs exprT_GetUAs
        exprT
        
        (* ILogicView*)
        
        ILogicPattern.mkEntails ILogicPattern.mkTrue ILogicPattern.mkFalse 
        ILogicPattern.mkAnd ILogicPattern.mkOr ILogicPattern.mkImpl
        ILogicPattern.mkExists ILogicPattern.mkForall
        
        ILogicPattern.fEntails ILogicPattern.fTrue ILogicPattern.fFalse ILogicPattern.fAnd 
        ILogicPattern.fOr ILogicPattern.fImpl ILogicPattern.fExists ILogicPattern.fForall
        ILogicView.RSym_ilfunc 
        
        ILogicView.funcD
        ILogicView.entailsR
	ILogicView.trueR
	ILogicView.falseR
	ILogicView.andR
	ILogicView.orR
	ILogicView.existsR
	ILogicView.forallR
        
        (* BILogicFunc *)
        
        BILogicPattern.mkEmp BILogicPattern.mkStar BILogicPattern.mkWand
        
        BILogicPattern.fEmp BILogicPattern.fStar BILogicPattern.fWand
        
        BILogicView.RSym_bilfunc
        
        BILogicView.funcD
	BILogicView.empR
	BILogicView.starR
	BILogicView.wandR
        
        BILogicView.typeof_bilfunc
        
        (* LaterFunc *)
        (*
          LaterFunc.mkLater
          
          LaterFunc.fLater
          
          LaterFunc.LaterFuncSumL LaterFunc.LaterFuncSumR LaterFunc.LaterFuncExpr          
          LaterFunc.RSym_later_func LaterFunc.LaterFuncInst
          
          LaterFunc.funcD LaterFunc.typ2_cast'
          
          LaterFunc.typeof_later_func
          
         (* EmbedFunc *)
         *)
        EmbedPattern.mkEmbed
        
        EmbedPattern.fEmbed
        
        EmbedView.RSym_embed_func 
        
        EmbedView.funcD 
        
	EmbedView.embedD
        
        EmbedView.typeof_embed_func
        
        (* EqView *)
        
        EqView.mkCons EqView.fEq EqView.RSym_EqFunc EqView.eq_func_symD EqView.eqR EqView.typeof_eq_func
        EqView.eq_func_eq EqView.typeof_eq_func
        
        (* StringView *)
        
        StringView.fString
        StringView.mkString
        
        StringView.RSym_StringFunc StringView.string_func_symD
        
        StringView.stringR
        
        StringView.typeofStringFunc
        
        (* NatView *)
        
        NatView.fNat
        NatView.mkNat
        
        NatView.RSym_NatFunc NatView.nat_func_symD
        
        NatView.natR
        
        NatView.typeofNatFunc
        
        (* BoolView *)
        
        BoolView.fBool
        BoolView.mkBool
        
        BoolView.RSym_BoolFunc BoolView.bool_func_symD
        
        BoolView.boolR
        
        BoolView.typeofBoolFunc
        (* BoolView *)
        
        BoolView.fBool
        BoolView.mkBool
        
        BoolView.RSym_BoolFunc BoolView.bool_func_symD
        
        BoolView.boolR
        
        BoolView.typeofBoolFunc
        
        (* ProdView *)
        
        ProdView.fPair
        ProdView.mkPair
        
        ProdView.RSym_ProdFunc ProdView.prod_func_symD
        
        ProdView.pairR
        
        ProdView.typeof_prod_func
        
        (* ListView *)
        
        ListView.fNil ListView.fCons
        ListView.mkNil ListView.mkCons
        
        ListView.RSym_ListFunc ListView.list_func_symD
        
        ListView.nilR ListView.consR
        
        ListView.typeof_list_func
        
        (* ListOpView *)
        
        ListOpView.fLength ListOpView.fNoDup ListOpView.fIn
        ListOpView.fMap ListOpView.fFold ListOpView.fCombine
        
        ListOpView.mkLength ListOpView.mkNoDup ListOpView.mkIn
        ListOpView.mkMap ListOpView.mkFold ListOpView.mkCombine
        
        ListOpView.RSym_ListOpFunc ListOpView.listOp_func_symD
        
        ListOpView.lengthR ListOpView.NoDupR ListOpView.InR
        ListOpView.mapR ListOpView.foldR ListOpView.combineR
        
        
        ListOpView.typeof_listOp_func
          
        (* ApView *)
        
        ApplicativeView.fPure ApplicativeView.fAp
        ApplicativeView.mkPure ApplicativeView.mkAp
          
        ApplicativeView.RSym_ApFunc ApplicativeView.ap_func_symD
       
        ApplicativeView.pureR ApplicativeView.apR
        
        ApplicativeView.typeof_ap_func
        
	(* OpenFunc *)
	
	SubstView.mkNull SubstView.mkStackGet
	SubstView.mkStackSet SubstView.mkApplySubst SubstView.mkSingleSubst SubstView.mkSubst
	SubstView.mkTruncSubst
	
	SubstView.fNull SubstView.fStackGet
	SubstView.fApplySubst SubstView.fSingleSubst SubstView.fSubst SubstView.fTruncSubst
	  
	SubstView.open_func_symD
	
	SubstView.typeof_subst_func SubstView.RSym_SubstFunc
        
	SubstView.stack_getR
	SubstView.stack_setR
	SubstView.applySubstR
	SubstView.singleSubstR
	
        
        (* JavaType *)
        
        Java.Func.Type.spec_match
        Java.Func.Type.TypeView_java_typ'
        Java.Func.Type.TypeView_java_typ
        Java.Func.Type.TypeViewOk_base_typ
        Java.Func.Type.TypeViewOk_java_typ
        JavaType.tyVal JavaType.tySpec JavaType.tyAsn
        JavaType.tyProg JavaType.tyMethod JavaType.tyCmd
        JavaType.tyDExpr
        Java.Func.JavaType.java_typD
        Java.Func.JavaType.tyFieldName
        Java.Func.JavaType.tyMethodName
        Java.Func.JavaType.tyClassName

        JavaType.fptrn_tyVal JavaType.fptrn_tySpec JavaType.fptrn_tyAsn
        JavaType.fptrn_tyProg JavaType.fptrn_tyMethod JavaType.fptrn_tyCmd
        JavaType.fptrn_tyDExpr JavaType.fptrn_tyMethodName
        JavaType.fptrn_tyClassName JavaType.fptrn_tyFieldName

        JavaType.ptrn_tyVal JavaType.ptrn_tySpec JavaType.ptrn_tyAsn
        JavaType.ptrn_tyProg JavaType.ptrn_tyMethod JavaType.ptrn_tyCmd
        JavaType.ptrn_tyDExpr JavaType.ptrn_tyClassName
        JavaType.ptrn_tyMethodName JavaType.ptrn_tyClassName

        Java.Func.JavaType.spec_match
        Java.Func.JavaType.asn_match
        Java.Func.JavaType.val_match
        Java.Func.Type.string_match
        Java.Func.JavaType.TSym_java_typ
        Java.Func.JavaType.java_typ_rect
        Java.Func.JavaType.java_typ_rec
        Java.Func.JavaType.java_typ_ind
        Java.Func.JavaType.java_typ_dec
 (*
        Typ2_Fun Typ0_Prop RType_typ typD Typ0_string Typ0_bool
        Typ0_val Typ0_nat Typ0_term Typ1_list Typ2_prod
        should_not_be_necessary should_also_not_be_necessary
        
        JavaType.bilops JavaType.ilops
        JavaType.eops (*JavaType.lops*)
*)        

        Java.Func.Type.asn_match
        Java.Func.Type.TypeView_base_typ
        Java.Func.Type.TypeView_base_typ'
        Java.Func.Type.prop_match
        Typ0_term
        Java.Func.Type.Typ2_tyArr Java.Func.Type.Typ0_tyProp Java.Func.Type.Typ0_tyNat 
        Java.Func.Type.Typ0_tyVal Java.Func.Type.Typ0_tyBool Java.Func.Type.Typ0_tyString
        Java.Func.Type.Typ1_tyList Java.Func.Type.Typ2_tyProd Java.Func.Type.RType_typ
        Java.Func.Type.TSym_typ' Java.Func.Type.TSymAll_typ_map

        (*   JavaType.typD *)

        (* MirrorCore.CTypes.CoreTypes *)

        MirrorCore.CTypes.CoreTypes.RType_ctyp
        MirrorCore.CTypes.CoreTypes.typ0D
        MirrorCore.CTypes.CoreTypes.typ1D
        MirrorCore.CTypes.CoreTypes.typ2D
        MirrorCore.CTypes.CoreTypes.Typ2_Fun
        MirrorCore.CTypes.CoreTypes.Typ0_Prop
        MirrorCore.CTypes.CoreTypes.RType_ctyp
        MirrorCore.CTypes.CoreTypes.ctyp_cast
        MirrorCore.CTypes.CoreTypes.ctyp_dec
        MirrorCore.CTypes.CoreTypes.ctypD
        MirrorCore.CTypes.CoreTypes.Typ0_sym
        MirrorCore.CTypes.CoreTypes.Typ1_sym
        MirrorCore.CTypes.CoreTypes.Typ2_sym
        MirrorCore.CTypes.CoreTypes.symbol_dec
        MirrorCore.CTypes.CoreTypes.type_for_arity
        MirrorCore.CTypes.CoreTypes.symbolD
        MirrorCore.CTypes.CoreTypes.applyn
        MirrorCore.CTypes.CoreTypes.applyn'
        MirrorCore.CTypes.CoreTypes.UIP_nat
        MirrorCore.CTypes.CoreTypes.Injective_tyApp

        MirrorCore.CTypes.TSymOneOf.TSymOneOf
        MirrorCore.CTypes.TSymOneOf.PartialViewOk_TSymOneOf
        MirrorCore.CTypes.TSymOneOf.PartialViewPMap_Type
        MirrorCore.CTypes.TSymOneOf.OneOfType.Injective_OneOf
        MirrorCore.CTypes.TSymOneOf.TSym_Empty_set
        MirrorCore.CTypes.TSymOneOf.TSym_All
        MirrorCore.CTypes.TSymOneOf.TSym_All_Empty
        MirrorCore.CTypes.TSymOneOf.TSym_All_Branch_None
        MirrorCore.CTypes.TSymOneOf.TSym_All_Branch_Some
        MirrorCore.CTypes.TSymOneOf.pmap_lookup'_Empty
        MirrorCore.CTypes.TSymOneOf.OneOfType.asNth
        MirrorCore.CTypes.TSymOneOf.OneOfType.asNth'
        MirrorCore.CTypes.TSymOneOf.OneOfType.asNth'_get_lookup
        MirrorCore.CTypes.TSymOneOf.OneOfType.asNth''
        MirrorCore.CTypes.TSymOneOf.OneOfType.OutOfF
        MirrorCore.CTypes.TSymOneOf.OneOfType.IntoF
        MirrorCore.CTypes.TSymOneOf.OneOfType.IntoF_OutOfF
        MirrorCore.CTypes.TSymOneOf.OneOfType.TypeR
        MirrorCore.CTypes.TSymOneOf.OneOfType.pmap_left
        MirrorCore.CTypes.TSymOneOf.OneOfType.pmap_right
        MirrorCore.CTypes.TSymOneOf.OneOfType.pmap_here
        MirrorCore.CTypes.TSymOneOf.OneOfType.pmap_lookup'
        MirrorCore.CTypes.TSymOneOf.OneOfType.pmap_insert
        MirrorCore.CTypes.TSymOneOf.OneOfType.indexF
        MirrorCore.CTypes.TSymOneOf.OneOfType.valueF

        Coq.Arith.PeanoNat.Nat.eq_dec
        Coq.Numbers.BinNums.positive_rect
        Coq.Numbers.BinNums.positive_rec
        Coq.Init.Logic.and_ind
        Coq.Init.Logic.and_rect
        Coq.Init.Logic.eq_ind_r
        Coq.Init.Logic.eq_ind
        Coq.Init.Logic.eq_rect
        Coq.Init.Logic.eq_rect_r
        Coq.Init.Logic.eq_rec
        Coq.Init.Logic.eq_sym
        Coq.Init.Logic.eq_trans
        Coq.Init.Logic.f_equal
        Coq.Init.Logic.False_rect
        Coq.Init.Logic.False_ind
(*        Coq.Init.Peano.O_S*)
        Coq.Init.Peano.eq_add_S
(*        Coq.Init.Peano.not_eq_S*)
        Coq.Init.Peano.f_equal_nat
        Coq.Init.Datatypes.nat_rect
        Coq.Init.Datatypes.nat_rec
        Coq.Init.Datatypes.idProp
        Coq.Init.Datatypes.IDProp
        Coq.Init.Specif.sumbool_rec
        Coq.Init.Specif.sumbool_rect

        (* ExtLib.Tactics.Injection *)

        ExtLib.Tactics.Injection.result
        ExtLib.Tactics.Injection.injection

        (* ExtLib.Data.Eq *)

        ExtLib.Data.Eq.internal_eq_sym_involutive
        ExtLib.Data.Eq.internal_eq_sym_internal

        ExtLib.Data.Eq.UIP_trans.uip_trans
        ExtLib.Data.Eq.UIP_trans.uip_prop_trans
        ExtLib.Data.Eq.eq_Arr_eq
        ExtLib.Data.Eq.eq_Const_eq

        (* ExtLib.Data.Vector *)

        ExtLib.Data.Vector.vector_dec
        ExtLib.Data.Vector.vector_hd
        ExtLib.Data.Vector.vector_tl
        ExtLib.Data.Vector.vector_map

	(* JavaFunc *)
        
        JavaFunc.Applicative_Fun        
        JavaFunc.RSym_ilfunc JavaFunc.RSym_bilfunc (*JavaFunc.RSym_embed_func*)
        ilops bilops eops is_pure func func_map RSym_JavaFunc typeof_java_func java_func_eq
        java_func_symD RelDec_java_func typeof_ilfunc
        OneOfType.list_to_pmap OneOfType.list_to_pmap_aux
        JavaFunc.Expr_expr
        mkPointstoVar
(*        JavaFunc.RSym_sub_func*)
        JavaFunc.RSym_func JavaFunc.java_env
        JavaFunc.fVal JavaFunc.fFields
        JavaFunc.fProg JavaFunc.fCmd JavaFunc.fDExpr JavaFunc.fFields
        JavaFunc.fMethodSpec JavaFunc.fProgEq JavaFunc.fTriple JavaFunc.fTypeOf
        JavaFunc.fFieldLookup JavaFunc.fPointsto JavaFunc.fNull
        JavaFunc.fPlusE JavaFunc.fMinusE JavaFunc.fTimesE JavaFunc.fAndE
        JavaFunc.fOrE JavaFunc.fNotE JavaFunc.fLtE JavaFunc.fValEq
        JavaFunc.mkTriple JavaFunc.mkFieldLookup JavaFunc.mkTypeOf
        JavaFunc.mkProgEq JavaFunc.mkExprList JavaFunc.evalDExpr
        JavaFunc.fMethodName JavaFunc.fClassName JavaFunc.fFieldName

        Java.Func.Type.val_match
        
        (* OTHER *)
        
        goalD Ctx.propD propD exprD_typ0 exprD split_env
        
        Nat.add
        Nat.pred
        snd
        fst
        not
        amap_substD
        substD
        SUBST.raw
        SUBST.raw_substD
        positive_ind positive_rect
        UVarMap.MAP.t
        UVarMap.MAP.key
        UVarMap.MAP.fold
        UVarMap.MAP.from_key
        FMapPositive.PositiveMap.key
        FMapPositive.PositiveMap.t
        FMapPositive.PositiveMap.fold
        FMapPositive.PositiveMap.xfoldi
        FMapPositive.append
        UVarMap.MAP.from_key
        pred
        plus
        Pos.to_nat
        Pos.succ
        Pos.iter_op
        Pos.eq_dec
        List.app
        HList.hlist_app
        Quant._foralls
        Quant._exists
        goalD_Prop
          
        View.f_insert
        SumN.pmap_lookup'
        (* FMapPositive *)
        FMapPositive.append
        FMapPositive.pmap_here
        FMapPositive.pmap_left
        FMapPositive.pmap_right
        FMapPositive.pmap_lookup
        FMapPositive.pmap_insert
        FMapPositive.branch
        FMapPositive.pmap_remove
        FMapPositive.pmap_empty
        FMapPositive.pmap_union
        
        Pos.add
        (* SymOneOf *)

        SymOneOf.internal_eq_rew_dep

        SymOneOf.OneOfType.pmap_lookup'
        SymOneOf.OneOfType.pmap_insert
        SymOneOf.OneOfType.pmap_here
        SymOneOf.OneOfType.pmap_left
        SymOneOf.OneOfType.pmap_right
        SymOneOf.OneOfType.Into
        SymOneOf.OneOfType.asNth'
        SymOneOf.OneOfType.asNth
        SymOneOf.OneOfType.OutOf
        SymOneOf.OneOfType.Injective_OneOf
        SymOneOf.OneOfType.asNth''
        SymOneOf.OneOfType.list_to_pmap
        SymOneOf.OneOfType.list_to_pmap_aux
        SymOneOf.OneOfType.TypeS
        SymOneOf.OneOfType.TypeR
        SymOneOf.typeof_sym_OneOf
        SymOneOf.RSymOneOf
        SymOneOf.symD_OneOf
        SymOneOf.RSym_All_Branch_Some

    ].

Ltac cbv_denote_tac a :=
  eval cbv [
      
      MirrorCore.syms.SymEnv.funcD
      MirrorCore.syms.SymEnv.RSym_func

      (* ExtLib.Data.Option *)

        ExtLib.Data.Option.Applicative_option
        ExtLib.Data.Option.eq_option_eq
        ExtLib.Data.Option.Injective_Some

      (* MirrorCore.Util.Quant *)
      
        MirrorCore.Util.Quant._impls 
        MirrorCore.Util.Quant._and
        MirrorCore.Util.Quant._foralls 
        MirrorCore.Util.Quant._exists 
 
      (* MirrorCore.OpenT *)
        
        MirrorCore.OpenT.OpenT
        MirrorCore.OpenT.Applicative_OpenT
        MirrorCore.OpenT.Functor_OpenT
        MirrorCore.OpenT.OpenT_Use
        MirrorCore.OpenT.OpenTrel
        MirrorCore.OpenT.OpenTeq
        MirrorCore.OpenT.Open_Abs
        MirrorCore.OpenT.Open_App

      (* MirrorCore.CTypes.CoreTypes *)

        MirrorCore.CTypes.CoreTypes.TypeView_sym0
        MirrorCore.CTypes.CoreTypes.TypeViewOk_sym0

      (* MirrorCore.CTypes.GenericTypes *)

        MirrorCore.CTypes.GenericTypes.symD

      (* MirrorCore.CTypes.BaseType *)

         MirrorCore.CTypes.BaseType.base_typ_rect
         MirrorCore.CTypes.BaseType.base_typ_rec
         MirrorCore.CTypes.BaseType.base_typ_ind
         MirrorCore.CTypes.BaseType.base_typ_dec
         MirrorCore.CTypes.BaseType.base_typD
         MirrorCore.CTypes.BaseType.prop_match
         MirrorCore.CTypes.BaseType.string_match
         MirrorCore.CTypes.BaseType.TSym_base_typ
         MirrorCore.CTypes.BaseType.tyProp
         MirrorCore.CTypes.BaseType.tyNat
         MirrorCore.CTypes.BaseType.tyBool
         MirrorCore.CTypes.BaseType.tyString

      (* MirrorCore.CTypes.List *)

         MirrorCore.CTypes.ListType.list_typ_rect
         MirrorCore.CTypes.ListType.list_typ_rec
         MirrorCore.CTypes.ListType.list_typ_ind
         MirrorCore.CTypes.ListType.list_typ_dec
         MirrorCore.CTypes.ListType.list_typD
         MirrorCore.CTypes.ListType.TSym_list_typ
         MirrorCore.CTypes.ListType.tyList

      (* MirrorCore.CTypes.Prod *)

         MirrorCore.CTypes.ProdType.prod_typ_rect
         MirrorCore.CTypes.ProdType.prod_typ_rec
         MirrorCore.CTypes.ProdType.prod_typ_ind
         MirrorCore.CTypes.ProdType.prod_typ_dec
         MirrorCore.CTypes.ProdType.prod_typD
         MirrorCore.CTypes.ProdType.TSym_prod_typ
         MirrorCore.CTypes.ProdType.tyProd

      (* MirrorCore.Views.View *)

         MirrorCore.Views.View.f_view
         MirrorCore.Views.View.pv_ok
         MirrorCore.Views.View.PartialView_trans
         MirrorCore.Views.View.PartialView_transOk

        Option.Applicative_option List.Traversable_list
        app amap_substD
        map
        MirrorCore.EnvI.tenv
(*        ExtLib.Structures.Applicative.pure*)
        ExtLib.Structures.Traversable.mapT
        ExtLib.Data.List.mapT_list
        Coq.Init.Wf.well_founded
        goalD_aux
        
	(* ExprD' *)
        exprD symAs typeof_sym typeof_expr type_cast
        MirrorCore.Lambda.ExprDsimul.ExprDenote.lambda_exprD
        lambda_exprD
        lambda_exprD_simul func_simul
        Expr.Expr_expr
        (* RSym *)
        
        SymSum.RSym_sum Rcast Relim Rsym eq_sym MirrorCore.SymI.symD(* RSym_env*)
        Rcast_val eq_rect_r eq_rect Datatypes.id
        RSym_Empty RSymOneOf typeof_sym_OneOf symD_OneOf sym_eqb_OneOf
        (* Monad *)
        
        Monad.bind Monad.ret
        
        OptionMonad.Monad_option
        
        (* HList *)
        
        HList.hlist_hd HList.hlist_tl
        
        (* TypesI *)
        MirrorCore.TypesI.Rty
        TypesI.Typ1_App
        TypesI.Typ2_App
        TypesI.typD 
        TypesI.RFun 
        typ2_match typ2 typ2_cast
        typ1_match typ1 typ1_cast
        typ0_match typ0 typ0_cast
        castR castD
        (* ExprI *)
        
        MirrorCore.VariablesI.Var ExprVariables.ExprVar_expr
        MirrorCore.VariablesI.UVar
        MirrorCore.Lambda.ExprVariables.ExprUVar_expr
        ExprI.exprT_Inj ExprI.exprT_UseV ExprI.exprT_UseU
        exprT_App ExprI.exprT
        HList.nth_error_get_hlist_nth 
        
        exprT_GetVAs exprT_GetUAs
        exprT
        
        (* ILogicView*)
        
        ILogicPattern.mkEntails ILogicPattern.mkTrue ILogicPattern.mkFalse 
        ILogicPattern.mkAnd ILogicPattern.mkOr ILogicPattern.mkImpl
        ILogicPattern.mkExists ILogicPattern.mkForall
        
        ILogicPattern.fEntails ILogicPattern.fTrue ILogicPattern.fFalse ILogicPattern.fAnd 
        ILogicPattern.fOr ILogicPattern.fImpl ILogicPattern.fExists ILogicPattern.fForall
        ILogicView.RSym_ilfunc 
        
        ILogicView.funcD
        ILogicView.entailsR
	ILogicView.trueR
	ILogicView.falseR
	ILogicView.andR
	ILogicView.orR
	ILogicView.existsR
	ILogicView.forallR
        
        (* BILogicFunc *)
        
        BILogicPattern.mkEmp BILogicPattern.mkStar BILogicPattern.mkWand
        
        BILogicPattern.fEmp BILogicPattern.fStar BILogicPattern.fWand
        
        BILogicView.RSym_bilfunc
        
        BILogicView.funcD
	BILogicView.empR
	BILogicView.starR
	BILogicView.wandR
        
        BILogicView.typeof_bilfunc
        
        (* LaterFunc *)
        (*
          LaterFunc.mkLater
          
          LaterFunc.fLater
          
          LaterFunc.LaterFuncSumL LaterFunc.LaterFuncSumR LaterFunc.LaterFuncExpr          
          LaterFunc.RSym_later_func LaterFunc.LaterFuncInst
          
          LaterFunc.funcD LaterFunc.typ2_cast'
          
          LaterFunc.typeof_later_func
          
         (* EmbedFunc *)
         *)
        EmbedPattern.mkEmbed
        
        EmbedPattern.fEmbed
        
        EmbedView.RSym_embed_func 
        
        EmbedView.funcD 
        
	EmbedView.embedD
        
        EmbedView.typeof_embed_func
        
        (* EqView *)
        
        EqView.mkCons EqView.fEq EqView.RSym_EqFunc EqView.eq_func_symD EqView.eqR EqView.typeof_eq_func
        EqView.eq_func_eq EqView.typeof_eq_func
        
        (* StringView *)
        
        StringView.fString
        StringView.mkString
        
        StringView.RSym_StringFunc StringView.string_func_symD
        
        StringView.stringR
        
        StringView.typeofStringFunc
        
        (* NatView *)
        
        NatView.fNat
        NatView.mkNat
        
        NatView.RSym_NatFunc NatView.nat_func_symD
        
        NatView.natR
        
        NatView.typeofNatFunc
        
        (* BoolView *)
        
        BoolView.fBool
        BoolView.mkBool
        
        BoolView.RSym_BoolFunc BoolView.bool_func_symD
        
        BoolView.boolR
        
        BoolView.typeofBoolFunc
        (* BoolView *)
        
        BoolView.fBool
        BoolView.mkBool
        
        BoolView.RSym_BoolFunc BoolView.bool_func_symD
        
        BoolView.boolR
        
        BoolView.typeofBoolFunc
        
        (* ProdView *)
        
        ProdView.fPair
        ProdView.mkPair
        
        ProdView.RSym_ProdFunc ProdView.prod_func_symD
        
        ProdView.pairR
        
        ProdView.typeof_prod_func
        
        (* ListView *)
        
        ListView.fNil ListView.fCons
        ListView.mkNil ListView.mkCons
        
        ListView.RSym_ListFunc ListView.list_func_symD
        
        ListView.nilR ListView.consR
        
        ListView.typeof_list_func
        
        (* ListOpView *)
        
        ListOpView.fLength ListOpView.fNoDup ListOpView.fIn
        ListOpView.fMap ListOpView.fFold ListOpView.fCombine
        
        ListOpView.mkLength ListOpView.mkNoDup ListOpView.mkIn
        ListOpView.mkMap ListOpView.mkFold ListOpView.mkCombine
        
        ListOpView.RSym_ListOpFunc ListOpView.listOp_func_symD
        
        ListOpView.lengthR ListOpView.NoDupR ListOpView.InR
        ListOpView.mapR ListOpView.foldR ListOpView.combineR
        
        
        ListOpView.typeof_listOp_func
          
        (* ApView *)
        
        ApplicativeView.fPure ApplicativeView.fAp
        ApplicativeView.mkPure ApplicativeView.mkAp
          
        ApplicativeView.RSym_ApFunc ApplicativeView.ap_func_symD
       
        ApplicativeView.pureR ApplicativeView.apR
        
        ApplicativeView.typeof_ap_func
        
	(* OpenFunc *)
	
	SubstView.mkNull SubstView.mkStackGet
	SubstView.mkStackSet SubstView.mkApplySubst SubstView.mkSingleSubst SubstView.mkSubst
	SubstView.mkTruncSubst
	
	SubstView.fNull SubstView.fStackGet
	SubstView.fApplySubst SubstView.fSingleSubst SubstView.fSubst SubstView.fTruncSubst
	  
	SubstView.open_func_symD
	
	SubstView.typeof_subst_func SubstView.RSym_SubstFunc
        
	SubstView.stack_getR
	SubstView.stack_setR
	SubstView.applySubstR
	SubstView.singleSubstR
	
        
        (* JavaType *)
        
        Java.Func.Type.spec_match
        Java.Func.Type.TypeView_java_typ'
        Java.Func.Type.TypeView_java_typ
        Java.Func.Type.TypeViewOk_base_typ
        Java.Func.Type.TypeViewOk_java_typ
        JavaType.tyVal JavaType.tySpec JavaType.tyAsn
        JavaType.tyProg JavaType.tyMethod JavaType.tyCmd
        JavaType.tyDExpr
        Java.Func.JavaType.java_typD
        Java.Func.JavaType.tyFieldName
        Java.Func.JavaType.tyMethodName
        Java.Func.JavaType.tyClassName

        JavaType.fptrn_tyVal JavaType.fptrn_tySpec JavaType.fptrn_tyAsn
        JavaType.fptrn_tyProg JavaType.fptrn_tyMethod JavaType.fptrn_tyCmd
        JavaType.fptrn_tyDExpr JavaType.fptrn_tyMethodName
        JavaType.fptrn_tyClassName JavaType.fptrn_tyFieldName

        JavaType.ptrn_tyVal JavaType.ptrn_tySpec JavaType.ptrn_tyAsn
        JavaType.ptrn_tyProg JavaType.ptrn_tyMethod JavaType.ptrn_tyCmd
        JavaType.ptrn_tyDExpr JavaType.ptrn_tyClassName
        JavaType.ptrn_tyMethodName JavaType.ptrn_tyClassName

        Java.Func.JavaType.spec_match
        Java.Func.JavaType.asn_match
        Java.Func.JavaType.val_match
        Java.Func.Type.string_match
        Java.Func.JavaType.TSym_java_typ
        Java.Func.JavaType.java_typ_rect
        Java.Func.JavaType.java_typ_rec
        Java.Func.JavaType.java_typ_ind
        Java.Func.JavaType.java_typ_dec
 (*
        Typ2_Fun Typ0_Prop RType_typ typD Typ0_string Typ0_bool
        Typ0_val Typ0_nat Typ0_term Typ1_list Typ2_prod
        should_not_be_necessary should_also_not_be_necessary
        
        JavaType.bilops JavaType.ilops
        JavaType.eops (*JavaType.lops*)
*)        

        Java.Func.Type.asn_match
        Java.Func.Type.TypeView_base_typ
        Java.Func.Type.TypeView_base_typ'
        Java.Func.Type.prop_match
        Typ0_term
        Java.Func.Type.Typ2_tyArr Java.Func.Type.Typ0_tyProp Java.Func.Type.Typ0_tyNat 
        Java.Func.Type.Typ0_tyVal Java.Func.Type.Typ0_tyBool Java.Func.Type.Typ0_tyString
        Java.Func.Type.Typ1_tyList Java.Func.Type.Typ2_tyProd Java.Func.Type.RType_typ
        Java.Func.Type.TSym_typ' Java.Func.Type.TSymAll_typ_map

        (*   JavaType.typD *)

        (* MirrorCore.CTypes.CoreTypes *)

        MirrorCore.CTypes.CoreTypes.RType_ctyp
        MirrorCore.CTypes.CoreTypes.typ0D
        MirrorCore.CTypes.CoreTypes.typ1D
        MirrorCore.CTypes.CoreTypes.typ2D
        MirrorCore.CTypes.CoreTypes.Typ2_Fun
        MirrorCore.CTypes.CoreTypes.Typ0_Prop
        MirrorCore.CTypes.CoreTypes.RType_ctyp
        MirrorCore.CTypes.CoreTypes.ctyp_cast
        MirrorCore.CTypes.CoreTypes.ctyp_dec
        MirrorCore.CTypes.CoreTypes.ctypD
        MirrorCore.CTypes.CoreTypes.Typ0_sym
        MirrorCore.CTypes.CoreTypes.Typ1_sym
        MirrorCore.CTypes.CoreTypes.Typ2_sym
        MirrorCore.CTypes.CoreTypes.symbol_dec
        MirrorCore.CTypes.CoreTypes.type_for_arity
        MirrorCore.CTypes.CoreTypes.symbolD
        MirrorCore.CTypes.CoreTypes.applyn
        MirrorCore.CTypes.CoreTypes.applyn'
        MirrorCore.CTypes.CoreTypes.UIP_nat
        MirrorCore.CTypes.CoreTypes.Injective_tyApp

        MirrorCore.CTypes.TSymOneOf.TSymOneOf
        MirrorCore.CTypes.TSymOneOf.PartialViewOk_TSymOneOf
        MirrorCore.CTypes.TSymOneOf.PartialViewPMap_Type
        MirrorCore.CTypes.TSymOneOf.OneOfType.Injective_OneOf
        MirrorCore.CTypes.TSymOneOf.TSym_Empty_set
        MirrorCore.CTypes.TSymOneOf.TSym_All
        MirrorCore.CTypes.TSymOneOf.TSym_All_Empty
        MirrorCore.CTypes.TSymOneOf.TSym_All_Branch_None
        MirrorCore.CTypes.TSymOneOf.TSym_All_Branch_Some
        MirrorCore.CTypes.TSymOneOf.pmap_lookup'_Empty
        MirrorCore.CTypes.TSymOneOf.OneOfType.asNth
        MirrorCore.CTypes.TSymOneOf.OneOfType.asNth'
        MirrorCore.CTypes.TSymOneOf.OneOfType.asNth'_get_lookup
        MirrorCore.CTypes.TSymOneOf.OneOfType.asNth''
        MirrorCore.CTypes.TSymOneOf.OneOfType.OutOfF
        MirrorCore.CTypes.TSymOneOf.OneOfType.IntoF
        MirrorCore.CTypes.TSymOneOf.OneOfType.IntoF_OutOfF
        MirrorCore.CTypes.TSymOneOf.OneOfType.TypeR
        MirrorCore.CTypes.TSymOneOf.OneOfType.pmap_left
        MirrorCore.CTypes.TSymOneOf.OneOfType.pmap_right
        MirrorCore.CTypes.TSymOneOf.OneOfType.pmap_here
        MirrorCore.CTypes.TSymOneOf.OneOfType.pmap_lookup'
        MirrorCore.CTypes.TSymOneOf.OneOfType.pmap_insert
        MirrorCore.CTypes.TSymOneOf.OneOfType.indexF
        MirrorCore.CTypes.TSymOneOf.OneOfType.valueF

        Coq.Arith.PeanoNat.Nat.eq_dec
        Coq.Numbers.BinNums.positive_rect
        Coq.Numbers.BinNums.positive_rec
        Coq.Init.Logic.and_ind
        Coq.Init.Logic.and_rect
        Coq.Init.Logic.eq_ind_r
        Coq.Init.Logic.eq_ind
        Coq.Init.Logic.eq_rect
        Coq.Init.Logic.eq_rect_r
        Coq.Init.Logic.eq_rec
        Coq.Init.Logic.eq_sym
        Coq.Init.Logic.eq_trans
        Coq.Init.Logic.f_equal
        Coq.Init.Logic.False_rect
        Coq.Init.Logic.False_ind
(*        Coq.Init.Peano.O_S*)
        Coq.Init.Peano.eq_add_S
(*        Coq.Init.Peano.not_eq_S*)
        Coq.Init.Peano.f_equal_nat
        Coq.Init.Datatypes.nat_rect
        Coq.Init.Datatypes.nat_rec
        Coq.Init.Datatypes.idProp
        Coq.Init.Datatypes.IDProp
        Coq.Init.Specif.sumbool_rec
        Coq.Init.Specif.sumbool_rect

        (* ExtLib.Tactics.Injection *)

        ExtLib.Tactics.Injection.result
        ExtLib.Tactics.Injection.injection

        (* ExtLib.Data.Eq *)

        ExtLib.Data.Eq.internal_eq_sym_involutive
        ExtLib.Data.Eq.internal_eq_sym_internal

        ExtLib.Data.Eq.UIP_trans.uip_trans
        ExtLib.Data.Eq.UIP_trans.uip_prop_trans
        ExtLib.Data.Eq.eq_Arr_eq
        ExtLib.Data.Eq.eq_Const_eq

        (* ExtLib.Data.Vector *)

        ExtLib.Data.Vector.vector_dec
        ExtLib.Data.Vector.vector_hd
        ExtLib.Data.Vector.vector_tl
        ExtLib.Data.Vector.vector_map

	(* JavaFunc *)
        
        JavaFunc.Applicative_Fun        
        JavaFunc.RSym_ilfunc JavaFunc.RSym_bilfunc (*JavaFunc.RSym_embed_func*)
        ilops bilops eops is_pure func func_map RSym_JavaFunc typeof_java_func java_func_eq
        java_func_symD RelDec_java_func typeof_ilfunc
        OneOfType.list_to_pmap OneOfType.list_to_pmap_aux
        JavaFunc.Expr_expr
        mkPointstoVar
(*        JavaFunc.RSym_sub_func*)
        JavaFunc.RSym_func JavaFunc.java_env
        JavaFunc.fVal JavaFunc.fFields
        JavaFunc.fProg JavaFunc.fCmd JavaFunc.fDExpr JavaFunc.fFields
        JavaFunc.fMethodSpec JavaFunc.fProgEq JavaFunc.fTriple JavaFunc.fTypeOf
        JavaFunc.fFieldLookup JavaFunc.fPointsto JavaFunc.fNull
        JavaFunc.fPlusE JavaFunc.fMinusE JavaFunc.fTimesE JavaFunc.fAndE
        JavaFunc.fOrE JavaFunc.fNotE JavaFunc.fLtE JavaFunc.fValEq
        JavaFunc.mkTriple JavaFunc.mkFieldLookup JavaFunc.mkTypeOf
        JavaFunc.mkProgEq JavaFunc.mkExprList JavaFunc.evalDExpr
        JavaFunc.fMethodName JavaFunc.fClassName JavaFunc.fFieldName

        Java.Func.Type.val_match
        
        (* OTHER *)
        
        goalD Ctx.propD propD exprD_typ0 exprD split_env
        
        Nat.add
        Nat.pred
        snd
        fst
        not
        amap_substD
        substD
        SUBST.raw
        SUBST.raw_substD
        positive_ind positive_rect
        UVarMap.MAP.t
        UVarMap.MAP.key
        UVarMap.MAP.fold
        UVarMap.MAP.from_key
        FMapPositive.PositiveMap.key
        FMapPositive.PositiveMap.t
        FMapPositive.PositiveMap.fold
        FMapPositive.PositiveMap.xfoldi
        FMapPositive.append
        UVarMap.MAP.from_key
        pred
        plus
        Pos.to_nat
        Pos.succ
        Pos.iter_op
        Pos.eq_dec
        List.app
        HList.hlist_app
        Quant._foralls
        Quant._exists
        goalD_Prop
          
        View.f_insert
        SumN.pmap_lookup'
        (* FMapPositive *)
        FMapPositive.append
        FMapPositive.pmap_here
        FMapPositive.pmap_left
        FMapPositive.pmap_right
        FMapPositive.pmap_lookup
        FMapPositive.pmap_insert
        FMapPositive.branch
        FMapPositive.pmap_remove
        FMapPositive.pmap_empty
        FMapPositive.pmap_union
        
        Pos.add
        (* SymOneOf *)

        SymOneOf.internal_eq_rew_dep

        SymOneOf.OneOfType.pmap_lookup'
        SymOneOf.OneOfType.pmap_insert
        SymOneOf.OneOfType.pmap_here
        SymOneOf.OneOfType.pmap_left
        SymOneOf.OneOfType.pmap_right
        SymOneOf.OneOfType.Into
        SymOneOf.OneOfType.asNth'
        SymOneOf.OneOfType.asNth
        SymOneOf.OneOfType.OutOf
        SymOneOf.OneOfType.Injective_OneOf
        SymOneOf.OneOfType.asNth''
        SymOneOf.OneOfType.list_to_pmap
        SymOneOf.OneOfType.list_to_pmap_aux
        SymOneOf.OneOfType.TypeS
        SymOneOf.OneOfType.TypeR
        SymOneOf.typeof_sym_OneOf
        SymOneOf.RSymOneOf
        SymOneOf.symD_OneOf
        SymOneOf.RSym_All_Branch_Some
    ] in a.

Let elem_ctor : forall x : typ, typD x -> @SymEnv.function _ _ :=
  @SymEnv.F _ _.

Ltac reify_aux reify term_table e n :=
  let k fs e :=
      pose e as n in
  reify_expr reify k
             [[ (fun (y : @mk_dvar_map _ _ _ _ term_table elem_ctor) => True) ]]
             [[ e ]].

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

Ltac run_rtac_print_code reify term_table tac_sound :=
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
	          let goal_result := constr:(run_tac tac (GGoal name)) in idtac goal_result
	        | None => idtac "expression " goal "is ill typed" t
	      end
	  end
	| _ => idtac tac_sound "is not a soudness theorem."
  end.

Ltac run_rtac_debug reify term_table tac_sound :=
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
	          idtac result;
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
 
