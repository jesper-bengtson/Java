Require Import MirrorCore.Reify.Reify.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.AbsAppI.
Require Import MirrorCore.RTac.RTac.
Require Import MirrorCore.Subst.FMapSubst.
Require Import MirrorCore.syms.SymOneOf.
Require Import MirrorCore.Views.FuncView.

Require Import Java.Func.JavaFunc.
Require Import Java.Func.JavaType.

Require Import Charge.Views.ILogicView.
Require Import Charge.Views.BILogicView.
Require Import Charge.Views.EmbedView.
Require Import Charge.Views.SubstView.
(*Require Import Charge.ModularFunc.LaterFunc.*)
Require Import MirrorCore.Views.NatView.
Require Import MirrorCore.Views.StringView.
Require Import MirrorCore.Views.BoolView.
Require Import MirrorCore.Views.ListView.
Require Import MirrorCore.Views.ListOpView.
Require Import MirrorCore.Views.ProdView.

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

Definition exprD_Prop (uvar_env var_env : env) (e : expr typ func) :=
  match exprD uvar_env var_env e tyProp with
    | Some e' => e' 
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
  
Definition run_tac tac goal :=
  runOnGoals tac nil nil 0 0 (CTop nil nil) 
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
  destruct Hsound as [Hwfs [Hwfg Hsound]].
  unfold Ctx.propD, exprD'_typ0 in Hsound.
  simpl in Hsound. unfold exprD_Prop, exprD; simpl.
  forward; inv_all; subst.

  destruct Hsound.
  inversion Hwfs; subst.
  simpl in H0; inv_all; subst.
  unfold pctxD in H0; inv_all; subst.
  apply H5.
  unfold goalD_Prop in He'. simpl in He'. forward; inv_all; subst.
Qed.

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
  unfold Ctx.propD, exprD'_typ0 in Hsound.
  unfold exprD_Prop.
  simpl in Hsound. unfold exprD. simpl. forward.
  destruct Hsound. 
  SearchAbout pctxD.
  inversion Hwfs; subst. simpl in H8. inv_all; subst.
  admit.
Admitted.

End Tactics.

Definition my_exprD' := @exprD' typ RType_typ (expr typ func).

Ltac cbv_denote :=
  cbv [
      goalD_aux
        
	(* ExprD' *)
        exprD' symAs  typeof_sym typeof_expr type_cast type_cast_typ
        exprD'_simul func_simul
        Expr.Expr_expr
        ExprDsimul.ExprDenote.exprD'
        (* RSym *)
        
        SymSum.RSym_sum Rcast Relim Rsym eq_sym symD(* RSym_env*)
        Rcast_val eq_rect_r eq_rect Datatypes.id
        RSym_Empty RSymOneOf typeof_sym_OneOf symD_OneOf sym_eqb_OneOf
        (* Monad *)
        
        Monad.bind Monad.ret
        
        OptionMonad.Monad_option
        
        (* HList *)
        
        HList.hlist_hd HList.hlist_tl
        
        (* TypesI *)
        TypesI.Typ1_App
        TypesI.Typ2_App
        TypesI.typD 
        typ2_match typ2 typ2_cast
        typ1_match typ1 typ1_cast
        typ0_match typ0 typ0_cast
        castR castD
        (* ExprI *)
        
        MirrorCore.VariablesI.Var ExprVariables.ExprVar_expr
        MirrorCore.VariablesI.UVar
        MirrorCore.Lambda.ExprVariables.ExprUVar_expr
        ExprI.exprT_Inj ExprI.exprT_UseV ExprI.exprT_UseU
        exprT_App ExprI.exprT OpenT
        HList.nth_error_get_hlist_nth 
        
        exprT_GetVAs exprT_GetUAs
        
        (* ILogicView*)
        
        ILogicView.mkEntails ILogicView.mkTrue ILogicView.mkFalse 
        ILogicView.mkAnd ILogicView.mkOr ILogicView.mkImpl
        ILogicView.mkExists ILogicView.mkForall
        
        ILogicView.fEntails ILogicView.fTrue ILogicView.fFalse ILogicView.fAnd 
        ILogicView.fOr ILogicView.fImpl ILogicView.fExists ILogicView.fForall
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
        
        BILogicView.mkEmp BILogicView.mkStar BILogicView.mkWand
        
        BILogicView.fEmp BILogicView.fStar BILogicView.fWand
        
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
        EmbedView.mkEmbed
        
        EmbedView.fEmbed
        
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
         
        Typ2_Fun Typ0_Prop RType_typ typD Typ0_string Typ0_bool
        Typ0_val Typ0_nat Typ0_term Typ1_list Typ2_prod
        should_not_be_necessary should_also_not_be_necessary
        
        JavaType.bilops JavaType.ilops
        JavaType.eops (*JavaType.lops*)
        
        (*   JavaType.typD *)
	(* JavaFunc *)
        
        
        JavaFunc.RSym_ilfunc JavaFunc.RSym_bilfunc JavaFunc.RSym_embed_func
        ilops (*is_pure*) func func_map RSym_JavaFunc typeof_java_func java_func_eq
        java_func_symD RelDec_java_func typeof_ilfunc
        list_to_pmap list_to_pmap_aux
        JavaFunc.Expr_expr
        mkPointstoVar
        JavaFunc.RSym_sub_func
        JavaFunc.RSym_func JavaFunc.java_env
        JavaFunc.fVal JavaFunc.fFields
        JavaFunc.fProg JavaFunc.fCmd JavaFunc.fDExpr JavaFunc.fFields
        JavaFunc.fMethodSpec JavaFunc.fProgEq JavaFunc.fTriple JavaFunc.fTypeOf
        JavaFunc.fFieldLookup JavaFunc.fPointsto JavaFunc.fNull
        JavaFunc.fPlusE JavaFunc.fMinusE JavaFunc.fTimesE JavaFunc.fAndE
        JavaFunc.fOrE JavaFunc.fNotE JavaFunc.fLtE JavaFunc.fValEq
        JavaFunc.mkTriple JavaFunc.mkFieldLookup JavaFunc.mkTypeOf
        JavaFunc.mkProgEq JavaFunc.mkExprList JavaFunc.evalDExpr
        
        (* OTHER *)
        
        goalD Ctx.propD propD exprD'_typ0 exprD split_env
        
        amap_substD
        substD
        SUBST.raw_substD
        UVarMap.MAP.fold
        FMapPositive.PositiveMap.fold
        FMapPositive.PositiveMap.xfoldi
        FMapPositive.append
        UVarMap.MAP.from_key
        pred
        plus
        Pos.to_nat
        Pos.succ
        Pos.iter_op
        List.app
        HList.hlist_app
        Quant._foralls
        Quant._exists
        goalD_Prop
          
        FuncView.f_insert
        SumN.pmap_lookup'
        (* FMapPositive *)
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
        SymOneOf.typeof_sym_OneOf

    ].

Let elem_ctor : forall x : typ, typD x -> @SymEnv.function _ _ :=
  @SymEnv.F _ _.

Ltac reify_aux reify term_table e n :=
  let k fs e :=
      pose e as n in
  reify_expr reify k
             [ (fun (y : @mk_dvar_map _ _ _ _ term_table elem_ctor) => True) ]
             [ e ].

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
 
