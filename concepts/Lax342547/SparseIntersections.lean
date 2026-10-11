import Lax342547.RawIntersections
import Lax342547.SparseRepresentatives

/-!
---
title: Sparse profiles from raw intersections (Lemma 4.4)
type: lemma
---
The explicit exceptional-set estimate and the deterministic shared-tensor
argument combine on the actual concrete moment profiles. The normalized
representatives are unique and have the paper's support and chiStar bounds.
-/

namespace Lax342547.SparseIntersections

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry
open Lax342547.CutProfiles Lax342547.CutSparsity Lax342547.ConcreteCut
open Lax342547.RawFrames Lax342547.RawIntersections Lax342547.SparseRepresentatives
open scoped ENNReal

axiom paper_sparse_parameters :
    let g := 10 ^ 9 + 1
    let D := 4000 * g
    1 ≤ D ∧ 8 * D < g * g ∧ 4 * D / g = 16000

axiom exists_concrete_scale (k b degree h : ℕ) :
    ∃ M₀ : ℕ, ∀ n : ℕ, 1 ≤ n →
      2 * (Fintype.card (Coordinate k n b degree) + h) + 1 ≤ M₀ * n ∧
      (4 : ℝ) * (Fintype.card (Coordinate k n b degree) + h : ℕ) ≤ (1 / 4 : ℝ) * (M₀ * n : ℕ) ∧
      (8 : ℝ) * Fintype.card (Component (Tag k)) ≤ (1 / 4 : ℝ) * (M₀ * n : ℕ) ∧
      ∀ D : ℕ, (Fintype.card (Component (Tag k)) * (2 * (Fintype.card (Coordinate k n b degree) + h)) * (2 * D) : ℕ) ≤
        (D : ℝ) * (M₀ * n : ℕ) / 4

axiom raw_intersections {k n b degree r h N : ℕ}
    (hr : 2 * r ≤ n) (hd : 1 ≤ degree) (M : Fin b → Matrix (Fin n) (Fin n) Binary)
    (D : ℕ) (hD : 1 ≤ D) (hsmall : 8 * D < (2 * k + 1) * (2 * k + 1))
    (hN : 2 * (Fintype.card (Coordinate k n b degree) + h) + 1 ≤ N)
    (hp : (4 : ℝ) * (Fintype.card (Coordinate k n b degree) + h : ℕ) ≤ (1 / 4 : ℝ) * N)
    (hc : (8 : ℝ) * Fintype.card (Component (Tag k)) ≤ (1 / 4 : ℝ) * N)
    (hcount : (Fintype.card (Component (Tag k)) * (2 * (Fintype.card (Coordinate k n b degree) + h)) * (2 * D) : ℕ) ≤
      (D : ℝ) * N / 4)
    (σ : PMF (Fin 2 → Component (Tag k) →
      Frame (Coordinate k n b degree) (Fin h) (Fin N) (selfGram hr hd M)))
    (hσ : ∀ o, σ o ≤ (2 : ℝ≥0∞) ^ (D * N) / Fintype.card (Fin 2 → Component (Tag k) →
      Frame (Coordinate k n b degree) (Fin h) (Fin N) (selfGram hr hd M))) :
    σ.toOuterMeasure {o | 2 * D < intersectionDimension o} ≤ (2 : ℝ≥0∞) ^ (-((D : ℝ) * N / 4)) ∧
      ∀ o : Fin 2 → Component (Tag k) →
        Frame (Coordinate k n b degree) (Fin h) (Fin N) (selfGram hr hd M),
        intersectionDimension o ≤ 2 * D →
        ∀ x y : Profile k n b degree, profileMap (o 0) x.val = profileMap (o 1) y.val →
          (∑ e, (x.val e).rank) ≤ 2 * D ∧ (∑ e, (y.val e).rank) ≤ 2 * D ∧
          ∃ w v : Representation k n b degree, Normalized x w ∧ Normalized y v ∧
            supportSize w.val ≤ 4 * D / (2 * k + 1) ∧ supportSize v.val ≤ 4 * D / (2 * k + 1) ∧
            chiStar hr w = chiStar hr v ∧
            (∀ u : Representation k n b degree, Normalized x u → u = w) ∧
            (∀ u : Representation k n b degree, Normalized y u → u = v)

end Lax342547.SparseIntersections
