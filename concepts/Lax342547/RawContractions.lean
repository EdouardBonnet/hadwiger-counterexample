import Lax342547.TableContractions

/-!
---
title: Actual frame observations realize the nominal channel contractions
type: lemma
---
The full cross forms of two raw units are their actual plus/minus Gram
pairings. Their primal/channel contractions agree with the original trace
contraction of frame tensors, on the whole profile space and hence on
every effective profile where a table is extended.
-/

namespace Lax342547.RawContractions

open Lax342547.MomentSpace Lax342547.RawFrames Lax342547.ExactPins Lax342547.ProjectedPins
open Lax342547.TableSpaces Lax342547.SmallTables Lax342547.TableContractions
open Lax342547.ReferencePins

variable {Comp B H N : Type} [Fintype B] [Fintype H] [Fintype N] {E : Matrix B B Binary}

def rawForms (oA oB : Fin 2 → Comp → Frame B H N E) : CrossForms Comp B H :=
  ⟨fun e => (dotProductBilin Binary Binary).compl₁₂ (observation oA (e, true))
      (observation oB (e, false)),
    fun e => (dotProductBilin Binary Binary).compl₁₂ (observation oB (e, true))
      (observation oA (e, false))⟩

axiom observation_blocks (o : Fin 2 → Comp → Frame B H N E) (e : Comp) (s : Bool) (i : Fin 2)
    (v : B → Binary) (w : H → Binary) :
    observation o (e, s) (primalEmbedding i v) =
      (if s then (o i e).P.mulVec v else (o i e).Q.mulVec v) ∧
    observation o (e, s) (channelEmbedding i w) =
      (if s then (o i e).X.mulVec w else (o i e).Y.mulVec w)

axiom raw_contraction [Fintype Comp] (oA oB : Fin 2 → Comp → Frame B H N E)
    (X : Submodule Binary (Comp → Matrix B B Binary)) (i z : Fin 2) (x : X) :
    fullContraction (rawForms oA oB) X i z x =
      profileContraction (oB z) (profileMap (oA i) x.val)

axiom raw_star_contraction [Fintype Comp] (oA oB : Fin 2 → Comp → Frame B H N E)
    {P Q : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N} (T : Table P Q)
    (hT : TableContractions.Extends (rawForms oA oB) T)
    (X : Submodule Binary (Comp → Matrix B B Binary)) (i z : Fin 2) (x : effective X P i) :
    starContraction T X i z x = profileContraction (oB z) (profileMap (oA i) x.val.val)

end Lax342547.RawContractions
