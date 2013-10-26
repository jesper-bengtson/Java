Require Import DecidableType DecidableTypeEx.
Require Import ZArith String.
Require Import Stack Open Util Pure.

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

Inductive sval : Set :=
| vint :> Z -> sval
| vbool :> bool -> sval
| vptr :> ptr -> sval
| nothing : sval.

Definition pnull := (0, EmptyString) : ptr.
Definition null := vptr pnull.

(* From here on, val will be (roughly) synonymous with sval *)
Instance SVal : ValNull := Build_ValNull nothing.

(* This lets sval unify with val *)
Canonical Structure SVal.

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

Definition val_to_int (v : val) :=
  match v with
    | vint n => n
    | _ => 0%Z
  end.

Definition val_to_bool (v : val) :=
  match v with 
    | vbool b => b
    | _ => false
  end.

Definition val_to_ptr (v : val) : ptr :=
  match v with
    | vptr p => p
    | _ => pnull
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

Definition pure_eval (e : dexpr) : pure := `eq (`val_to_bool (eval e)) (`true).

Definition eval_exprs (s : stack) (es : list dexpr) :=
  map (fun e => eval_aux s e) es.

Definition field  := string.
Definition method := string.

Inductive cmd :=
| cassign : var -> dexpr -> cmd
| cskip   : cmd
| cseq    : cmd -> cmd -> cmd
| cif     : dexpr -> cmd -> cmd -> cmd
| cwhile  : dexpr -> cmd -> cmd
| cwrite  : var -> field -> dexpr -> cmd
| cread   : var -> var -> field -> cmd
| calloc  : var -> class -> cmd
| cdcall  : var -> var -> method -> list dexpr -> cmd
| cscall  : var -> class -> method -> list dexpr -> cmd
| cassert : dexpr -> cmd
.

(* The set of stack variables potentially modified by a command *)
Fixpoint modifies (c: cmd) :=
  match c with
  | cassign x _    => SS.singleton x
  | cskip          => SS.empty
  | cseq c1 c2     => SS.union (modifies c1) (modifies c2)
  | cif _ c1 c2    => SS.union (modifies c1) (modifies c2)
  | cwhile _ c     => modifies c
  | cwrite _ _ _   => SS.empty
  | cread x _ _    => SS.singleton x
  | calloc x _     => SS.singleton x
  | cdcall x _ _ _ => SS.singleton x
  | cscall x _ _ _ => SS.singleton x
  | cassert _      => SS.empty
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
