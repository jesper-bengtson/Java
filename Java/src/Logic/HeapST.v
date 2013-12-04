Require Import RelationClasses Setoid Morphisms Program. 
Require Import MapInterface MapFacts.
Require Import SepAlg SepAlgMap UUSepAlg SepAlgInsts Stack Lang Rel.

Local Existing Instance MapSepAlgOps.
Local Existing Instance MapSepAlg.
Local Existing Instance MapEquiv.
Local Existing Instance EquivPreorder.
Local Existing Instance UUMapSepAlg.

(* Inductive datatype sST: [s]hape-of-[S]ession-[T]ype
 * A outline of a session-type with only the shape of the protocol.
 * So it only contains the ordering of messages, not their assertions
 * too.
 * Stored on the heap.
 *)
Inductive sST : Type := 
 | close : sST
 | input : sST -> sST
 | output : sST -> sST.

Definition heap_st := Map [stptr, sST].
Definition heap_st_unit : heap_st := @map_unit _ _ _ sST.

Instance RelHeapST : Rel heap_st := _.
Instance PreorderHeapST : PreOrder (@rel heap_st RelHeapST) := _.
Instance HeapSTSepAlgOps : SepAlgOps heap_st := _.
Instance SepAlgHeapST : UUSepAlg heap_st := _.


Fixpoint sST_dual (p: sST) : sST :=
  match p with
    | close => close
    | input p => output (sST_dual p)
    | output p => input (sST_dual p)
  end.
  
