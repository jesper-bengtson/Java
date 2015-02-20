Require Import MirrorCore.RTac.Core.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Lambda.ExprUnify_simul.

Require Import Java.Func.JavaFunc.
Require Import Java.Func.JavaType.
Require Import Java.Language.Program.

Require Import Charge.ModularFunc.BaseFunc.

Section MethodLookup.
  Context {fs : Environment}.

  Definition METHOD_LOOKUP : rtac typ (expr typ func) :=
    fun tus tvs n m c s e =>
      match e with
        | App (App (App (App (Inj (inr pMethodLookup)) (pProg P)) C) m) M =>
		  match baseS C, baseS m with
		    | Some (pConst tyString C'), Some (pConst tyString m') =>
		      match method_lookup' C' m' P with
		        | Some Method =>
		          match @exprUnify (ctx_subst c) typ func _ _ _ _ _ 3
		                           tus tvs 0 M (mkMethod Method) tyMethod s with
		            | Some s => Solved s
		            | None   => Fail
		          end
			    | _ => Fail
			  end
	        | _, _ => Fail
		  end
        | _ => Fail
      end.

End MethodLookup.