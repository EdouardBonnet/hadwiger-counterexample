import Lax342547.RawFrames
import Lax342547.ConcreteGeometry
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
---
title: Rank and trace of shared frame tensors
type: lemma
---
Injective primal frame maps preserve coefficient-matrix rank. A tensor
shared by two endpoints has its column space in their primal-span
intersection. Its trace is the entrywise pairing with the self-Gram matrix.
-/

namespace Lax342547.TensorIntersections

open Lax342547.MomentSpace Lax342547.RawFrames Lax342547.ConcreteGeometry

variable {B H N : Type} [Fintype B] [Fintype H] [Fintype N]

def intersectionSpace (P Q : Matrix N B Binary) : Submodule Binary (N → Binary) :=
  LinearMap.range P.mulVecLin ⊓ LinearMap.range Q.mulVecLin

axiom sandwich_rank {E : Matrix B B Binary} (F : Frame B H N E)
    (w : Matrix B B Binary) : (sandwich F.P F.Q w).rank = w.rank

axiom shared_rank {E : Matrix B B Binary} (F G : Frame B H N E)
    (w v : Matrix B B Binary) (h : sandwich F.P F.Q w = sandwich G.P G.Q v) :
    w.rank = v.rank ∧ w.rank ≤ Module.finrank Binary (intersectionSpace F.P G.P)

axiom shared_total_rank {Comp : Type} [Fintype Comp] {E : Matrix B B Binary}
    (F G : Comp → Frame B H N E) (w v : Comp → Matrix B B Binary)
    (h : profileMap F w = profileMap G v) :
    (∑ e, (w e).rank) = ∑ e, (v e).rank ∧
      (∑ e, (w e).rank) ≤ ∑ e, Module.finrank Binary (intersectionSpace (F e).P (G e).P)

axiom trace_sandwich {E : Matrix B B Binary} (F : Frame B H N E)
    (w : Matrix B B Binary) : Matrix.trace (sandwich F.P F.Q w) = matrixPair E w

end Lax342547.TensorIntersections
