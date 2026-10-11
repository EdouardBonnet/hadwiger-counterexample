import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
---
title: Paired-frame orbit under the primal and dual actions
type: lemma
---
Lemma 4.1: two individually injective pairs of frames with equal Gram
pairings differ by one ambient linear automorphism, acting contragrediently
on the dual frame. No nondegeneracy of the prescribed Gram is needed.
-/

namespace Lax342547.PairedFrames

universe u v w z

variable {K : Type u} {U : Type v} {V : Type w} {W : Type z} [Field K]
  [AddCommGroup U] [Module K U]
  [AddCommGroup V] [Module K V] [hVdim : FiniteDimensional K V]
  [AddCommGroup W] [Module K W]

axiom paired_frame_orbit {K : Type u} {U : Type v} {V : Type w} {W : Type z} [Field K]
    [AddCommGroup U] [Module K U]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W]
    (A A' : U →ₗ[K] V) (B B' : W →ₗ[K] Module.Dual K V)
    (hA : Function.Injective A) (hA' : Function.Injective A')
    (hB : Function.Injective B) (hB' : Function.Injective B')
    (hgram : ∀ u w, B w (A u) = B' w (A' u)) :
    ∃ L : V ≃ₗ[K] V, (∀ u, L (A u) = A' u) ∧
      ∀ w v, B w (L.symm v) = B' w v

axiom paired_matrix_orbit {I J N : Type} [Fintype I] [Fintype J] [Fintype N]
    [DecidableEq N] (A A' : Matrix N I K) (B B' : Matrix N J K)
    (hA : Function.Injective A.mulVec) (hA' : Function.Injective A'.mulVec)
    (hB : Function.Injective B.mulVec) (hB' : Function.Injective B'.mulVec)
    (hgram : A.transpose * B = A'.transpose * B') :
    ∃ C D : Matrix N N K, C * D = 1 ∧ D * C = 1 ∧
      C * A = A' ∧ D.transpose * B = B'

end Lax342547.PairedFrames
