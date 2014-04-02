Require Import DecidableType DecidableTypeEx.
Require Import ZArith String.
Require Import Stack Open Util OpenILogic.
Require Import Compare_dec.
Require Import OrderedType OrderedTypeEx.
Require Import SepAlgMap.

Module string_DT' <: MiniDecidableType.
  Definition t := string.
  Definition eq_dec := string_dec.
End string_DT'.
Module string_DT <: UsualDecidableType := Make_UDT string_DT'.

Module SS  := FSetWeakList.Make(string_DT).
Module SS' := WSetMore_fun (string_DT) SS.

Module SM  := FMapWeakList.Make(string_DT).
Module SM' := WMapMore_fun (string_DT) SM.

Definition class := string.
Definition var := string.
Definition ptr := (nat * class)%type.
Definition arrptr := nat.
Definition stptr := nat.
Definition protocol := nat.

Inductive sval : Set :=
| vint :> Z -> sval
| vbool :> bool -> sval
| vptr :> ptr -> sval
| varr :> arrptr -> sval
| vst :> stptr -> sval
| nothing : sval.

Definition pnull := (0, EmptyString) : ptr.
Definition null := vptr pnull.

(* From here on, val will be (roughly) synonymous with sval *)
Instance SVal : ValNull := Build_ValNull nothing.

(* This lets sval unify with val *)
Canonical Structure SVal.


Inductive svalEq : sval -> sval -> Prop :=
| s_int (a b : Z) : a === b -> svalEq (vint a) (vint b)
| s_bool (a b : bool) : a === b -> svalEq (vbool a) (vbool b)
| s_ptr (a b : ptr) : a === b -> svalEq (vptr a) (vptr b)
| s_arrptr (a b : arrptr) : a === b -> svalEq (varr a) (varr b)
| s_stptr (a b : stptr) : a === b -> svalEq (vst a) (vst b)
| s_nothing : svalEq nothing nothing
.
Definition SvalEqEquiv : Equivalence svalEq.
Proof.
  split.
  * unfold Reflexive; intros x; induction x; constructor; auto.
  * unfold Symmetric; intros x y Hxy.
    induction Hxy; constructor; auto.
  * unfold Transitive; intros x y z Hxy Hyz.
    inversion Hxy; subst; inversion Hyz; subst;
    constructor; transitivity b; assumption.
Qed.

Inductive sval_lt : sval -> sval -> Prop :=
| s_lt_int_int (a b : Z) : a <<< b -> sval_lt (vint a) (vint b)
| s_lt_bool_bool (a b : bool): a <<< b -> sval_lt (vbool a) (vbool b)
| s_lt_ptr_ptr (a b : ptr) : a <<< b -> sval_lt (vptr a) (vptr b)
| s_lt_arr_arr (a b : arrptr) : a <<< b -> sval_lt (varr a) (varr b)
| s_lt_st_st (a b : stptr) : a <<< b -> sval_lt (vst a) (vst b)

| s_lt_nothing_int b : sval_lt nothing (vint b)

| s_lt_nothing_bool b : sval_lt nothing (vbool b)
| s_lt_int_bool a b : sval_lt (vint a) (vbool b)

| s_lt_nothing_ptr b : sval_lt nothing (vptr b)
| s_lt_int_ptr a b : sval_lt (vint a) (vptr b)
| s_lt_bool_ptr a b : sval_lt (vbool a) (vptr b)

| s_lt_nothing_arr b : sval_lt nothing (varr b)
| s_lt_int_arr a b : sval_lt (vint a) (varr b)
| s_lt_bool_arr a b : sval_lt (vbool a) (varr b)
| s_lt_ptr_arr a b : sval_lt (vptr a) (varr b)

| s_lt_nothing_st b : sval_lt nothing (vst b)
| s_lt_int_st a b : sval_lt (vint a) (vst b)
| s_lt_bool_st a b : sval_lt (vbool a) (vst b)
| s_lt_ptr_st a b : sval_lt (vptr a) (vst b)
| s_lt_arr_st a b : sval_lt (varr a) (vst b)
.
Definition sval_compare a b :=
  match a, b with
      | nothing, nothing => Eq
      | nothing, _ => Lt
      | _, nothing => Gt

      | vint a', vint b' => a' =?= b'
      | vint a', _ => Lt
      | _, vint b' => Gt

      | vbool a', vbool b' => a' =?= b'
      | vbool a', _ => Lt
      | _, vbool b' => Gt

      | vptr a', vptr b' => a' =?= b'
      | vptr b', _ => Lt
      | _, vptr b' => Gt

      | varr a', varr b' => a' =?= b'
      | varr a', _ => Lt
      | _, varr b' => Gt

      | vst a', vst b' => a' =?= b'
  end.
Local Existing Instance SvalEqEquiv.
Definition StrictOrderSval : StrictOrder sval_lt svalEq.
Proof.
  split.
  * intros a b c Hab Hbc.
    inversion Hab; subst;
    inversion Hbc; subst;
    constructor; transitivity b0; assumption.
  * intros x y Hxy H; induction Hxy; inversion H; try (inversion H2);
    apply lt_not_eq in H0; apply H0; apply H3.
Qed.

Local Existing Instance StrictOrderSval.
Program Definition OrderedTypeSval : OrderedType sval := Build_OrderedType sval svalEq sval_lt _ _ sval_compare _.
Next Obligation.
  destruct x; destruct y; simpl; repeat constructor.
  * destruct (compare_dec z z0); repeat constructor; auto.
  * destruct (compare_dec b b0); repeat constructor; auto.
  * destruct (compare_dec p p0); repeat constructor; auto.
  * destruct (compare_dec a a0); repeat constructor; auto.
  * destruct (compare_dec s s0); repeat constructor; auto.
Qed.

Definition stack := stack var.

Inductive dexpr : Type :=
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

Definition val_to_stptr (v : val) : stptr :=
  match v with
    | vst n => n
    | _ => 0
  end.
 
Definition val_class : val -> class := fun v => snd(val_to_ptr v).

Fixpoint eval_aux (s : stack) (e : dexpr) : val :=
  match e with
    | E_val v => v
    | E_var v => s v
    | E_plus e1 e2 => vint (val_to_int (eval_aux s e1) + val_to_int (eval_aux s e2))
    | E_minus e1 e2 => vint (val_to_int (eval_aux s e1) - val_to_int (eval_aux s e2))
    | E_times e1 e2 => vint (val_to_int (eval_aux s e1) * val_to_int (eval_aux s e2))
    | E_and e1 e2 => vbool (val_to_bool (eval_aux s e1) && val_to_bool (eval_aux s e2))
    | E_or e1 e2 => vbool (val_to_bool (eval_aux s e1) || val_to_bool (eval_aux s e2))
    | E_not e => vbool (negb (val_to_bool (eval_aux s e)))
    | E_lt e1 e2 => vbool (Zlt_bool (val_to_int (eval_aux s e1)) (val_to_int (eval_aux s e2)))
    | E_eq e1 e2 => vbool true
  end.

Program Definition eval e : expr := fun s => eval_aux s e.

Definition vlogic_eval (e : dexpr) : vlogic := `eq (`val_to_bool (eval e)) (`true).

Definition eval_exprs (s : stack) (es : list dexpr) :=
  map (fun e => eval_aux s e) es.

Definition field  := string.
Definition method := string.

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
| csend     : var -> var -> cmd
| crecv     : var -> var -> cmd
| cstart    : var -> class -> method -> cmd
.

(* The set of stack variables potentially modified by a command *)
Fixpoint modifies (c: cmd) :=
  match c with
  | cassign x _    => SS.singleton x
  | cseq c1 c2     => SS.union (modifies c1) (modifies c2)
  | cif _ c1 c2    => SS.union (modifies c1) (modifies c2)
  | cwhile _ c     => modifies c
  | cread x _ _    => SS.singleton x
  | carrread x _ _ => SS.singleton x
  | carralloc x _  => SS.singleton x
  | calloc x _     => SS.singleton x
  | cdcall x _ _ _ => SS.singleton x
  | cscall x _ _ _ => SS.singleton x
  | crecv v _      => SS.singleton v
  | cstart x _ _   => SS.singleton x
  |  _             => SS.empty
  end.

Notation " x 'A=' e "  := (cassign x e) (at level 60, no associativity) : cmd_scope.
Notation " x 'R=' e '[' f ']' "  := (cread x e f) (at level 60, e at level 59, no associativity) : cmd_scope.
Notation " e '[' f ']' 'W=' g " := (cwrite e f g) (at level 60, no associativity) : cmd_scope.
Notation " x 'D=' e '[' m ']' args " := (cdcall x e m args) (at level 60, e at level 59, m at level 9, no associativity) : cmd_scope.
Notation " x 'S=' C '::' m args " := (cscall x C m args) (at level 60, C at level 40, m at level 9, no associativity) : cmd_scope.
Notation " x 'N=' 'alloc' C " := (calloc x C) (at level 60, no associativity) : cmd_scope.

Notation " x 'st=' 'start' C '::' m " := (cstart x C m) (at level 60, no associativity) : cmd_scope.
Notation " x 'st=' 'recv' c " := (crecv x c) (at level 60, no associativity) : cmd_scope.
Notation " 'send' c x " := (csend c x) (at level 60, no associativity) : cmd_scope.

Notation " c1 ';;' c2 " := (cseq c1 c2) (at level 70, right associativity) : cmd_scope.
Notation "'Skip'" := cskip : cmd_scope.
Notation "'If' e 'Then' c1 'Else' c2" := (cif e c1 c2) (at level 65) : cmd_scope.
Notation "'While' e 'Do' c" := (cwhile e c) (at level 65) : cmd_scope.

Arguments Scope cscall [ _ _ _ list_scope ].
Arguments Scope cdcall [ _ _ _ list_scope ].
