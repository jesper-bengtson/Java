Require Import MirrorCore.Reify.Reify.
Require Import MirrorCore.Reify.ReifyView. 
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.syms.SymOneOf.
Require Import MirrorCore.Lib.ListView.
Require Import MirrorCore.Lib.ListOpView.
Require Import MirrorCore.Lib.ApplicativeView.
Require Import MirrorCore.Lib.ProdView.
Require Import MirrorCore.Lib.EqView.
Require Import MirrorCore.Lib.NatView.
Require Import MirrorCore.Lib.StringView.
Require Import MirrorCore.Lib.BoolView.
Require Import MirrorCore.Lib.ProdView.
Require Import MirrorCore.CTypes.CoreTypes.
Require Import MirrorCore.CTypes.BaseType.
Require Import MirrorCore.CTypes.ListType.
Require Import MirrorCore.CTypes.ProdType.

Require Import Java.Logic.AssertionLogic.
Require Import Java.Logic.SpecLogic.
Require Import Java.Language.Program.
Require Import Java.Language.Lang.
Require Import Java.Semantics.OperationalSemantics.
Require Import Java.Func.JavaFunc.
Require Import Java.Func.JavaType.
Require Import Java.Func.Type.

Require Import Charge.Views.ILogicView.
Require Import Charge.Views.BILogicView.
Require Import Charge.Views.EmbedView.
Require Import Charge.Views.SubstView.

Require Import Charge.Reify.ILogicReify.
Require Import Charge.Reify.BILogicReify.
Require Import Charge.Reify.EmbedReify.

Require Import ChargeCore.Open.Stack.
Require Import ChargeCore.Open.Subst.
Require Import ChargeCore.Open.OpenILogic.
Require Import ChargeCore.Logics.ILogic.
Require Import ChargeCore.Logics.BILogic.
Require Import ChargeCore.Logics.Later.

Require Import ExtLib.Structures.Applicative.
Require Import MirrorCore.Lib.NatView.

Reify Declare Typed Table term_table : BinNums.positive => typ.

Local Instance Applicative_Fun A : Applicative (RFun A) :=
{ pure := fun _ x _ => x
; ap := fun _ _ f x y => (f y) (x y)
}.

Global Instance Reify_typ : Reify typ :=
  Reify_typ typ (reify_base_typ typ ::
                 reify_list_typ typ ::
                 reify_prod_typ typ ::
                 reify_subst_typ typ _ Lang.var val ::
                 reify_java_typ typ :: nil).

Global Instance Reify_java : Reify (expr typ func) :=
  Reify_func typ func (reify_java_func ::
                                  reify_nat typ func ::
                                  reify_bool typ func ::
                                  reify_eq typ func ::
                                  reify_applicative typ func (RFun (String.string -> val)) ::
                                  reify_list typ func :: 
                                  reify_listOp typ func :: 
                                  reify_prod typ func ::
                                  reify_string typ func ::
          	                  reify_ilogic typ func :: 
          	                  reify_plogic typ func :: 
                                  reify_bilogic typ func ::
                                  reify_embed typ func ::
                                  reify_subst typ func String.string val :: nil).

Reify Declare Syntax reify_typ := reify_scheme@{Set} typ.
Reify Declare Syntax reify_java := reify_scheme@{Set} (expr typ func).

Let elem_ctor : forall x : typ, typD x -> @SymEnv.function _ _ :=
  @SymEnv.F _ _.

Ltac reify_java e :=
  let k fs e :=
      pose e in
  reify_expr reify_java k
             [[ (fun (y : @mk_dvar_map _ _ _ _ term_table elem_ctor) => True) ]]
             [[ e ]].

Local Instance fs : Environment := 
  Build_Environment (FMapPositive.PositiveMap.empty (SymEnv.function typ _)).

Ltac reify_java_debug e :=
  let n := fresh "n" in
  let k fs e :=
      pose e as n in
  reify_expr reify_java k
             [[ (fun (y : @mk_dvar_map _ _ _ _ term_table elem_ctor) => True) ]]
             [[ e ]];
  let t := eval cbv in (@typeof_expr typ func RType_typ _ RSym_func nil nil n) in
                          idtac t.

Ltac reify_typ e :=
  let k fs e :=
      pose e in
  reify_expr reify_typ k
             [[ (fun (y : @mk_dvar_map _ _ _ _ term_table elem_ctor) => True) ]]
             [[ e ]].

Notation "'ap_eq' '[' x ',' y ']'" :=
	 (ap (T := RFun (String.string -> val)) (ap (T := RFun (String.string -> val)) (pure (T := RFun (String.string -> val)) (@eq val)) x) y).
Notation "'ap_pointsto' '[' x ',' f ',' e ']'" :=
	(ap (T := RFun (String.string -> val)) (ap (T := RFun (String.string -> val)) (ap (T := RFun (String.string -> val))
		(pure (T := RFun (String.string -> val)) pointsto) (stack_get x))
			(pure (T := RFun (String.string -> val)) f)) e).
Notation "'ap_typeof' '[' e ',' C ']'" :=
	(ap (T := RFun (String.string -> val))
	    (ap (T := RFun (String.string -> val))
	        (pure (T := RFun (String.string -> val)) typeof)
	        (pure (T := RFun (String.string -> val)) C))
	    e).


Goal (forall (Pr : Program) (C : class) (v : val) (x : String.string) (f : field) (fields : list field) (ex : (RFun (String.string -> val) val)), True).
  intros Pr C v x f fields ex.
  reify_java_debug 5.
  reify_java_debug (typeof C v).
  reify_java_debug (field_lookup).
  reify_java_debug (5::4::3::@nil nat).
  reify_java_debug (field_lookup Pr C fields).
  reify_java_debug True.
  reify_java_debug False.
  reify_java_debug (True \/ False).
  reify_java_debug (True /\ False).
  reify_java_debug (False -> True).
  reify_java_debug (5 = 5).
  reify_java_debug (exists x, x = 5).
  reify_java_debug (forall x, x = 5).

  reify_java_debug (stack_get (val := val) x).
  reify_java_debug (pure (T := RFun (String.string -> val)) pointsto).
  reify_java_debug (Applicative.pure (T := RFun (String.string -> val)) 5).
  reify_typ Lang.var.

  reify_java_debug (ap (T := RFun (String.string -> val))
                     (pure (T := RFun (String.string -> val)) pointsto)
                     (stack_get (val := val) x)).

  reify_java_debug (ap (T := RFun (String.string -> val)) 
                       (ap (T := RFun (String.string -> val)) 
                           (pure (T := RFun (String.string -> val)) pointsto) 
                     (stack_get x)) 
                 (pure (T := RFun (String.string -> val)) f)).

  reify_java_debug (fun a b c => pointsto a b c).


  pose (E_val (vint 3)) as d.

  reify_java_debug (pure (T := RFun (String.string -> val)) (vbool true)).

  reify_java_debug (forall x : nat, x = x).

  reify_java_debug (ap (T := RFun (String.string -> val)) (pure (T := RFun (String.string -> val)) (@eq val)) (eval d)).

  reify_java_debug (ap_pointsto [x, f, (eval d)]).

  generalize String.EmptyString. intro c.
  reify_java_debug (cread c c c).

   reify_java_debug (ltrue |-- triple ltrue ltrue (cread c c c)).
   reify_java_debug (ltrue |-- {[ ltrue ]} cread c c c {[ ltrue ]}).

  reify_java_debug cskip.

  reify_java_debug (forall P, P /\ P).

  reify_java_debug (forall x : nat, x = x).
  reify_java_debug (exists x : nat, x = x).

  reify_java_debug (@subst1 String.string val _).
  reify_java_debug (cseq cskip cskip).

  reify_java_debug (@map nat nat).
  reify_java_debug (ILogic.lentails True True).

  reify_java_debug ((True -> False) -> True).
  reify_java_debug (forall P Q, P /\ Q).

  reify_java_debug (forall P : sasn, ILogic.lentails ILogic.ltrue P).
  reify_java_debug (forall (G : spec) (P Q : sasn), ILogic.lentails G (triple P Q cskip)).
  generalize (String.EmptyString : String.string).
  intro y.

  reify_java_debug (stack_get (A := String.string) (val := val)).
  reify_java_debug (@stack_get String.string val y).

  reify_java_debug (stack_get (val := val) x).

  reify_java_debug (y = y).

  reify_java_debug (@ltrue sasn _).

  reify_java_debug (eval (E_not (E_val v))).
  reify_java_debug (pure (T := RFun (String.string -> val)) (vbool true)).

Require Import ChargeCore.Logics.ILEmbed.

  reify_java_debug
    (@embed ((String.string -> val) -> Prop) sasn _ 
            (ap_eq [eval (E_not (E_val v)), pure (vbool true)]) //\\ ltrue).
  

  exact I.

Defined.