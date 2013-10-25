Require Import ILogic ILInsts Rel.
Require Import Open Stack.

Local Existing Instance ILFun_Ops.
Local Existing Instance ILFun_ILogic.

Section Pure.
  Context {A : Type} {Heq : DecidableEq A}.
  Context {B : Type} `{HIL : ILogic B}.
  Context {V : ValNull}.

  Definition pure := @open A V Prop.

  Definition open_eq {T} (a b : open T) : pure :=
    fun s => a s = b s.

  Global Instance ILOpsPure : ILogicOps pure := _.
  Global Instance ILogicPure : ILogic pure := _.

End Pure.