Require Import DecidableType DecidableTypeEx.
Require Import ZArith Coq.Strings.String.

Require Import Java.Util.

Require Import Coq.Bool.Bool.

Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.String.
Require Import ExtLib.Data.Z.
Require Import ExtLib.Data.List.
Require Import ExtLib.Tactics.Consider.

Require Import ChargeCore.Open.Stack.
Require Import ChargeCore.Open.Open.
Require Import ChargeCore.Open.OpenILogic.
Require Import ChargeCore.Open.Subst.

Definition class : Set := String.string.
Definition var : Set := String.string.
Definition ptr : Set := (nat * class)%type.
Definition arrptr : Set := nat.

Instance RelDec_ptr : RelDec (@eq ptr) := {
	rel_dec p1 p2 :=
	match p1, p2 with
		| (x, c), (y, d) => (x ?[ eq ] y && c ?[ eq ] d)%bool
	end
}.

Instance RelDec_Correct_ptr : RelDec_Correct RelDec_ptr.
Proof.
  split; intros; destruct x, y; simpl.
  consider (n ?[ eq ] n0); intros;
  consider (c ?[ eq ] c0); intros; subst; simpl; try intuition congruence.
Defined.

Inductive val : Set :=
| vint :> Z -> val
| vbool :> bool -> val
| vptr :> ptr -> val
| varr :> arrptr -> val
| nothing : val.

Instance RelDec_val : RelDec (@eq val) := {
  rel_dec v1 v2 :=
  	match v1, v2 with
	  | vint x, vint y => x ?[ eq ] y
	  | vbool a, vbool b => a ?[ eq ] b
	  | vptr p, vptr q => p ?[ eq ] q
	  | varr p, varr q => p ?[ eq ] q
	  | nothing, nothing => true
	  | _, _ => false
	end
}.

Instance RelDec_Correct_val : RelDec_Correct RelDec_val.
Proof.
  split; intros; destruct x, y; simpl; try intuition congruence.
  + consider (z ?[ eq ] z0); intros; subst; intuition congruence.
  + consider (b ?[ eq ] b0); intros; subst; intuition congruence.
  + consider (p ?[ eq ] p0); intros; subst; intuition congruence.
  + consider (a ?[ eq ] a0); intros; subst; intuition congruence.
Qed.

Definition pnull := (0, EmptyString) : ptr.
Definition null := vptr pnull.

(* From here on, val will be (roughly) synonymous with val *)
Instance Val : ValNull val := Build_ValNull nothing.

(* This lets val unify with val *)
Canonical Structure Val.

Definition stack := stack var val.

Inductive dexpr : Set :=
| E_val   : val -> dexpr
| E_var   : var -> dexpr
| E_plus  : dexpr -> dexpr -> dexpr
| E_minus : dexpr -> dexpr -> dexpr
| E_times : dexpr -> dexpr -> dexpr
| E_and   : dexpr -> dexpr -> dexpr
| E_or    : dexpr -> dexpr -> dexpr
| E_not   : dexpr -> dexpr
| E_lt    : dexpr -> dexpr -> dexpr
| E_eq    : dexpr -> dexpr -> dexpr.

Fixpoint beq_dexpr e1' e2' :=
  match e1', e2' with
  | E_val v1, E_val v2 => v1 ?[ eq ] v2
  | E_var x, E_var y => x ?[ eq ] y
  | E_plus e1 e2, E_plus e3 e4 => beq_dexpr e1 e3 && beq_dexpr e2 e4
  | E_minus e1 e2, E_minus e3 e4 => beq_dexpr e1 e3 && beq_dexpr e2 e4
  | E_times e1 e2, E_times e3 e4 => beq_dexpr e1 e3 && beq_dexpr e2 e4
  | E_and e1 e2, E_and e3 e4 => beq_dexpr e1 e3 && beq_dexpr e2 e4
  | E_or e1 e2, E_or e3 e4 => beq_dexpr e1 e3 && beq_dexpr e2 e4
  | E_not e1, E_not e2 => beq_dexpr e1 e2
  | E_lt e1 e2, E_lt e3 e4 => beq_dexpr e1 e3 && beq_dexpr e2 e4
  | E_eq e1 e2, E_eq e3 e4 => beq_dexpr e1 e3 && beq_dexpr e2 e4
  | _, _ => false
  end.

Instance RelDec_dexpr : RelDec (@eq dexpr) := {
  rel_dec := beq_dexpr
}.

Instance RelDec_Correct_dexpr : RelDec_Correct RelDec_dexpr.
Proof.
	split; intro x; induction x; simpl in *; intros; try intuition congruence.
	+ destruct y; simpl in *; try intuition congruence.
	  consider (v ?[ eq ] v0); intuition congruence.
	+ destruct y; simpl in *; try intuition congruence.
	  consider (v ?[ eq ] v0); intuition congruence.
	+ destruct y; simpl in *; try intuition congruence.
	  rewrite andb_true_iff, IHx1, IHx2; intuition congruence.
	+ destruct y; simpl in *; try intuition congruence.
	  rewrite andb_true_iff, IHx1, IHx2; intuition congruence.
	+ destruct y; simpl in *; try intuition congruence.
	  rewrite andb_true_iff, IHx1, IHx2; intuition congruence.
	+ destruct y; simpl in *; try intuition congruence.
	  rewrite andb_true_iff, IHx1, IHx2; intuition congruence.
	+ destruct y; simpl in *; try intuition congruence.
	  rewrite andb_true_iff, IHx1, IHx2; intuition congruence.
	+ destruct y; simpl in *; try intuition congruence.
	  rewrite IHx; intuition congruence.
	+ destruct y; simpl in *; try intuition congruence.
	  rewrite andb_true_iff, IHx1, IHx2; intuition congruence.
	+ destruct y; simpl in *; try intuition congruence.
	  rewrite andb_true_iff, IHx1, IHx2; intuition congruence.
Qed.

Definition val_to_int (v : val) : Z :=
  match v with
    | vint n => n
    | _ => 0%Z
  end.

Definition val_to_bool (v : val) : bool :=
  match v with
    | vbool b => b
    | _ => false
  end.

Definition val_to_ptr (v : val) : ptr :=
  match v with
    | vptr p => p
    | _ => pnull
  end.

Definition val_to_arr (v : val) : arrptr :=
  match v with
    | varr n => n
    | _ => 0
  end.

Definition val_to_nat (v : val) : nat :=
  Z.to_nat (val_to_int v).

Definition val_class : val -> class := fun v => snd(val_to_ptr v).

Definition eplus e1 e2 := vint (val_to_int e1 + val_to_int e2).
Definition eminus e1 e2 := vint (val_to_int e1 - val_to_int e2).
Definition etimes e1 e2 := vint (val_to_int e1 * val_to_int e2).
Definition eand e1 e2 := vbool (val_to_bool e1 && val_to_bool e2).
Definition eor e1 e2 := vbool (val_to_bool e1 || val_to_bool e2).
Definition enot e := vbool (negb (val_to_bool e)).
Definition elt e1 e2 := vbool (Zlt_bool (val_to_int e1) (val_to_int e2)).
Definition eeq (e1 e2 : val) := vbool (e1 ?[ eq ] e2).

Fixpoint eval_aux (s : stack) (e : dexpr) : val :=
  match e with
    | E_val v => v
    | E_var v => s v
    | E_plus e1 e2 => eplus (eval_aux s e1) (eval_aux s e2)
    | E_minus e1 e2 => eminus (eval_aux s e1) (eval_aux s e2)
    | E_times e1 e2 => etimes (eval_aux s e1) (eval_aux s e2)
    | E_and e1 e2 => eand (eval_aux s e1) (eval_aux s e2)
    | E_or e1 e2 => eor (eval_aux s e1) (eval_aux s e2)
    | E_not e => enot (eval_aux s e)
    | E_lt e1 e2 => elt (eval_aux s e1) (eval_aux s e2)
    | E_eq e1 e2 => eeq (eval_aux s e1) (eval_aux s e2)
  end.

Program Definition eval e : expr := fun s => eval_aux s e.

Definition vlogic_eval (e : dexpr) : vlogic := fun s => eval e s = true.
(*
`eq ( eval e) (`true).
*)
(*fun s => eval e s = true.*)

Definition eval_exprs (s : stack) (es : list dexpr) :=
  map (fun e => eval_aux s e) es.

Definition field : Set := String.string.
Definition method : Set := String.string.

Global Instance RelDec_var : RelDec (@eq var) := RelDec_string.
Global Instance RelDec_method : RelDec (@eq var) := RelDec_string.
Global Instance RelDec_class : RelDec (@eq var) := RelDec_string.
Global Instance RelDec_field : RelDec (@eq var) := RelDec_string.

Inductive cmd :=
| cassign   : var -> dexpr -> cmd
| cskip     : cmd
| cseq      : cmd -> cmd -> cmd
| cif       : dexpr -> cmd -> cmd -> cmd
| cwhile    : dexpr -> cmd -> cmd
| cwrite    : var -> field -> dexpr -> cmd
| cread     : var -> var -> field -> cmd
| carrread  : var -> var -> list dexpr -> cmd
| carrwrite : var -> list dexpr -> dexpr -> cmd
| carralloc : var -> dexpr -> cmd
| calloc    : var -> class -> cmd
| cdcall    : var -> var -> method -> list dexpr -> cmd
| cscall    : var -> class -> method -> list dexpr -> cmd
| cassert   : dexpr -> cmd
.
(* Possible bug in Coq when c1 and c2 matches in the cases *)
Fixpoint beq_cmd cmd1 cmd2 :=
	match cmd1, cmd2 with
	    | cassign v1 e1, cassign v2 e2 => v1 ?[ eq ] v2 && e1 ?[ eq ] e2
		| cskip, cskip => true
		| cseq c1 c2, cseq c3 c4 => beq_cmd c1 c3 && beq_cmd c2 c4
		| cif e1 c1 c2, cif e2 c3 c4 => e1 ?[ eq ] e2 && beq_cmd c1 c3 && beq_cmd c2 c4
		| cwhile e1 c1, cwhile e2 c2 => e1 ?[ eq ] e2 && beq_cmd c1 c2
		| cwrite v1 f1 e1, cwrite v2 f2 e2 => v1 ?[ eq ] v2 && f1 ?[ eq ] f2 && e1 ?[ eq ] e2
		| cread v1 v2 f1, cread v3 v4 f2 => v1 ?[ eq ] v3 && v2 ?[ eq ] v4 && f1 ?[ eq ] f2
		| carrread v1 v2 es1, carrread v3 v4 es2 => v1 ?[ eq ] v3 && v2 ?[ eq ] v4 && es1 ?[ eq ] es2
		| carrwrite v1 es1 e1, carrwrite v2 es2 e2 => v1 ?[ eq ] v2 && es1 ?[ eq ] es2 && e1 ?[ eq ] e2
		| calloc v1 c1, calloc v2 c2 => v1 ?[ eq ] v2 && c1 ?[ eq ] c2
		| carralloc v1 d1, carralloc v2 d2 => v1 ?[ eq ] v2 && d1 ?[ eq ] d2
		| cdcall v1 v2 m1 es1, cdcall v3 v4 m2 es2 => v1 ?[ eq ] v3 && v2 ?[ eq ] v4 && m1 ?[ eq ] m2 && es1 ?[ eq ] es2
		| cscall v1 c1 m1 es1, cscall v2 c2 m2 es2 => v1 ?[ eq ] v2 && c1 ?[ eq ] c2 && m1 ?[ eq ] m2 && es1 ?[ eq ] es2
		| cassert e1, cassert e2 => e1 ?[ eq ] e2
		| _, _ => false
    end.

Instance RelDec_cmd : RelDec (@eq cmd) := {
  rel_dec := beq_cmd
}.

Instance RelDec_Correct_cmd  : RelDec_Correct RelDec_cmd.
Proof.
	split; intro c; induction c; intros; simpl in *.
	+ destruct y; unfold rel_dec; simpl; try intuition congruence.
	  rewrite andb_true_iff.
	  consider (v ?[ eq ] v0); consider (d ?[ eq ] d0); intuition congruence.
	+ destruct y; unfold rel_dec; simpl; try intuition congruence.
	+ destruct y; unfold rel_dec; simpl; try intuition congruence.
	  rewrite andb_true_iff, IHc1, IHc2; intuition congruence.
	+ destruct y; unfold rel_dec; simpl; try intuition congruence.
	  do 2 rewrite andb_true_iff; rewrite IHc1, IHc2.
	  consider (d ?[ eq ] d0); intuition congruence.
	+ destruct y; unfold rel_dec; simpl; try intuition congruence.
	  rewrite andb_true_iff, IHc.
	  consider (d ?[ eq ] d0); intuition congruence.
	+ destruct y; unfold rel_dec; simpl; try intuition congruence.
	  consider (v ?[ eq ] v0); consider (f ?[ eq ] f0); consider (d ?[ eq ] d0);
	    simpl; intuition congruence.
	+ destruct y; unfold rel_dec; simpl; try intuition congruence.
	  consider (v ?[ eq ] v1); consider (v0 ?[ eq ] v2); consider (f ?[ eq ] f0);
	    simpl; intuition congruence.
	+ destruct y; unfold rel_dec; simpl; try intuition congruence.
	  consider (v ?[ eq ] v1); consider (v0 ?[ eq ] v2); consider (l ?[ eq ] l0);
	    simpl; intuition congruence.
	+ destruct y; unfold rel_dec; simpl; try intuition congruence.
	  consider (v ?[ eq ] v0); consider (l ?[ eq ] l0); consider (d ?[ eq ] d0);
	    simpl; intuition congruence.
	+ destruct y; unfold rel_dec; simpl; try intuition congruence.
	  consider (v ?[ eq ] v0); consider (d ?[ eq ] d0); simpl; intuition congruence.
	+ destruct y; unfold rel_dec; simpl; try intuition congruence.
	  consider (v ?[ eq ] v0); consider (c ?[ eq ] c0); simpl; intuition congruence.
	+ destruct y; unfold rel_dec; simpl; try intuition congruence.
	  consider (v ?[ eq ] v1); consider (v0 ?[ eq ] v2); consider (m ?[ eq ] m0);
	    consider (l ?[ eq ] l0); simpl; intuition congruence.
	+ destruct y; unfold rel_dec; simpl; try intuition congruence.
	  consider (v ?[ eq ] v0); consider (c ?[ eq ] c0); consider (m ?[ eq ] m0);
	    consider (l ?[ eq ] l0); simpl; try intuition congruence.
	+ destruct y; unfold rel_dec; simpl; try intuition congruence.
	  consider (d ?[ eq ] d0); try intuition congruence.
Qed.


(* The set of stack variables potentially modified by a command *)
Fixpoint modifies (c: cmd) :=
  match c with
  | cseq c1 c2     => app (modifies c1) (modifies c2)
  | cif _ c1 c2    => app (modifies c1) (modifies c2)
  | cwhile _ c     => modifies c
  | cassign x _
  | cread x _ _
  | carrread x _ _
  | carralloc x _
  | calloc x _
  | cdcall x _ _ _
  | cscall x _ _ _ => x::nil
  |  _             => nil
  end.

Notation " x 'A=' e "  := (cassign x e) (at level 60, no associativity) : cmd_scope.
Notation " x 'R=' e '[' f ']' "  := (cread x e f) (at level 60, e at level 59, no associativity) : cmd_scope.
Notation " e '[' f ']' 'W=' g " := (cwrite e f g) (at level 60, no associativity) : cmd_scope.
Notation " x 'D=' e '[' m ']' args " := (cdcall x e m args) (at level 60, e at level 59, m at level 9, no associativity) : cmd_scope.
Notation " x 'S=' C '::' m args " := (cscall x C m args) (at level 60, C at level 40, m at level 9, no associativity) : cmd_scope.
Notation " x 'N=' 'alloc' C " := (calloc x C) (at level 60, no associativity) : cmd_scope.

Notation " c1 ';;' c2 " := (cseq c1 c2) (at level 70, right associativity) : cmd_scope.
Notation "'Skip'" := cskip : cmd_scope.
Notation "'If' e 'Then' c1 'Else' c2" := (cif e c1 c2) (at level 65) : cmd_scope.
Notation "'While' e 'Do' c" := (cwhile e c) (at level 65) : cmd_scope.

Arguments Scope cscall [ _ _ _ list_scope ].
Arguments Scope cdcall [ _ _ _ list_scope ].
