Require Import ChargeCore.Logics.ILogic.
Require Import ChargeCore.Logics.BILogic.
Require Import ChargeCore.Logics.ILEmbed.
Require Import ChargeCore.Open.OpenILogic.
Require Import ChargeCore.Open.Subst.
Require Import ChargeCore.Open.Stack.

Require Import Java.Language.Lang.
Require Import Java.Language.Program.

Require Import Java.Semantics.OperationalSemantics.

Require Import Java.Logic.SpecLogic.
Require Import Java.Logic.AssertionLogic.

Require Import ExtLib.Data.PreFun.
Require Import ExtLib.Structures.Applicative.

Require Import Java.Func.Reify.

Set Implicit Arguments.
Set Strict Implicit.

Local Instance Applicative_Fun A : Applicative (RFun A) :=
{ pure := fun _ x _ => x
; ap := fun _ _ f x y => (f y) (x y)
}.

Lemma pull_exists {A} {P : A -> sasn} c Q G
	(H : forall x, G |-- {[P x]} c {[Q]}) :
	G |-- {[lexists P]} c {[Q]}.
Proof.
  rewrite <- exists_into_precond2.
  apply lforallR. apply H.
Qed.

Lemma eq_to_subst x (e : Lang.stack -> val) (P Q : sasn) 
    (H : apply_subst P (subst1 e x) |-- apply_subst Q (subst1 e x)) :
	embed (ap_eq [stack_get x, e]) //\\ P |-- Q.
Proof.
  
  admit.
Admitted.

Lemma ent_right_exists {A} (P : sasn) (Q : A -> sasn)
	(H : exists x, P |-- Q x) :
	P |-- lexists Q.
Proof.
  admit.
Admitted.

Lemma ent_left_exists {A} (P : A -> sasn) (Q : sasn)
	(H : forall x : A, P x |-- Q) :
	lexists P |-- Q.
Proof.
  admit.
Admitted.

Lemma rule_seq c1 c2 (P Q R : sasn) G
      (Hc1 : G |-- {[P]} c1 {[Q]})
      (Hc2 : G |-- {[Q]} c2 {[R]}) :
  G |-- {[P]} cseq c1 c2 {[R]}.
Proof.
  admit.
(*  apply rule_seq with Q; assumption.  *)
Admitted.

Lemma rule_skip P Q G : P |-- Q -> G |-- {[P]} cskip {[Q]}.
Proof.
  intros.
  admit.
(*  eapply roc_post; [eapply rule_skip | apply H].*)
Admitted.
	
Lemma rule_skip2 P G :(* P |-- Q -> *)G |-- {[P]} cskip {[P]}.
Proof.
  apply rule_skip. reflexivity.
Qed.

Lemma rule_if (e : dexpr) c1 c2 (P Q : sasn) G
      (Hc1 : G |-- {[(@embed (@vlogic Lang.var val) sasn _ 
                      (ap_eq [eval e, pure (vbool true)])) //\\ P]} c1 {[Q]})
      (Hc2 : G |-- {[(@embed (@vlogic Lang.var _) sasn _ 
                      (ap_eq [eval (E_not e), pure (vbool true)])) //\\ P]} c2 {[Q]}) : 
  G |-- {[P]} cif e c1 c2 {[Q]}. 
Proof.
  admit.
(*
  reify_imp (G |-- {[P]} cif e c1 c2 {[Q]}).
  eapply rule_if; unfold vlogic_eval, Open.liftn, Open.lift; simpl in *;
  	[apply Hc1|apply Hc2].*)
Admitted.

  Lemma rule_read_fwd (x y : String.string) (f : field) (e : RFun (RFun String.string val) val) (P Q : RFun (RFun String.string val) asn) (G : spec)
    (HP : P |-- ap_pointsto [y, f, e])
    (HQ : Exists v : val, (embed (ap_eq [stack_get x, apply_subst e (subst1 (pure (T := RFun (RFun String.string val)) v) x)])) //\\
    					      (apply_subst P (subst1 (pure (T := RFun (RFun String.string val)) v) x)) |-- Q) :
    G |-- {[ P ]} cread x y f {[ Q ]}.
  Proof.
    admit.
(*
    pose proof @rule_read_fwd x y f e P. 
    unfold Open.liftn, Open.lift, open_eq, stack_get, Open.var_expr in *; simpl in *.
    rewrite <- HQ , <- H; [apply ltrueR | apply HP].
*)
    Admitted.


  Lemma rule_write_fwd (x : String.string) (f : field) (e : dexpr) G (P Q F : RFun (RFun String.string val) asn) (e' : RFun (RFun String.string val) val)
        (HP : P |-- ap_pointsto [x, f, e'] ** F) 
        (HQ : ap_pointsto [x, f, eval e] ** F |-- Q) :
    G |-- ({[ P ]} cwrite x f e {[ Q ]}).
  Proof.
    admit.
(*
     pose proof @rule_write_frame G P F x f e' e. unfold Open.liftn, Open.lift, open_eq, stack_get, Open.var_expr in *; simpl in *.
	 rewrite <- HQ, H.
	 unfold stack. unfold pointsto. unfold eval.
	 
	 setoid_rewrite <- sepSPC1 at 2.
	 reflexivity. 
	 rewrite HP. 
	 setoid_rewrite <- sepSPC1 at 2.
	 reflexivity.
*)
  Admitted.
  Lemma rule_assign_fwd (x : Lang.var) (e : dexpr) G P :
    G |-- {[ P ]} cassign x e {[ Exists v : val,
                                 embed (ap_eq [stack_get x, 
                                               apply_subst (eval e) (subst1 (pure (T := Fun stack) v) x)]) //\\ 
    							   (apply_subst P (subst1 (pure (T := Fun stack) v) x)) ]}.
  Proof.
    admit.
(*
    pose proof @rule_assign_fwd G P.
    apply H. reflexivity.
*)
  Admitted.

  Lemma rule_alloc_fwd (x : Lang.var) (C : class) (G : spec) (P Q : sasn) (fields : list field) (Pr : Program) 
	(Heq : G |-- prog_eq Pr)
	(Hf : field_lookup Pr C fields) 
	(Hent : Exists p : val, embed (ap_typeof [stack_get x, C]) //\\
	                                            embed (ap_eq [stack_get x, pure p]) //\\
	                                            fold_right (fun f P => ap_pointsto [x, f, pure null] ** P)
	                                                    (apply_subst P (subst1 (pure (T := Fun stack) p) x)) fields |-- Q) :
	G |-- {[ P ]} calloc x C {[ Q ]}.
  Proof.
  	admit.
  Admitted.
(*
  Lemma rule_static_complete (x : Lang.var) C (m : String.string) (es : list dexpr) (ps : list String.string) (r : Lang.var) G
    (P Q F Pm Qm : sasn)
    (HSpec : G |-- |> method_spec C m ps r Pm Qm)
    (HPre: P |-- apply_subst Pm (substl_trunc (zip ps (@map _ (stack -> val) eval es))) ** F)
    (HLen: length ps = length es) :
          G |-- {[ P ]} cscall x C m es {[ Exists v:val, apply_subst Qm (substl_trunc (zip (@cons String.string r ps) 
                                     (@cons (stack -> val) (stack_get x)
                                      (@map (stack -> val) _ (fun e => apply_subst e (subst1 (pure (T := Fun stack) v) x)) 
                                          (@map dexpr (stack -> val) eval es))))) ** 
                           apply_subst F (subst1 (pure (T := Fun stack) v) x)]}.
Proof.
	admit.
Admitted.

Lemma rule_dynamic_complete (x y : Lang.var) (m : String.string) (es : list dexpr) (ps : list String.string) C (r : Lang.var) G
    (P Q F Pm Qm : sasn)
    (HSpec : G |-- |> method_spec C m ps r Pm Qm)
    (HPre: P |-- (embed (ap_typeof [stack_get y, C]) //\\ 
                  apply_subst Pm (substl_trunc (zip ps (@map _ (stack -> val) eval (E_var y :: es))))) ** 
                 F)
    (HPost : Exists v:val, embed (ap_typeof [apply_subst (stack_get y) (subst1 (pure (T := Fun stack) v) x), C]) //\\
                    apply_subst Qm (substl_trunc (zip (@cons String.string r ps) 
                    (@cons (stack -> val) (stack_get x) (@cons (stack -> val) (apply_subst (stack_get y) (subst1 (pure (T := Fun stack) v) x))
			        (@map (stack -> val) _ (fun e => apply_subst e (subst1 (pure (T := Fun stack) v) x)) 
			        (@map dexpr (stack -> val) eval es)))))) ** 
                    apply_subst F (subst1 (pure (T := Fun stack) v) x) |-- Q)
    (HLen: length ps = length (E_var y :: es)) :
           G |-- {[ P ]} cdcall x y m es {[ Q ]}.
Proof.
    eapply rule_dcall_forward.
    eassumption.
    rewrite HPre. 
    reflexivity.
    assumption.
    rewrite <- HPost.
    reflexivity.
Qed.
*)
