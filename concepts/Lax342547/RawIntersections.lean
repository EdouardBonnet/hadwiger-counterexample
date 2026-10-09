import Lax342547.ImageScale
import Lax342547.TensorIntersections
import Lax342547.KernelWitness

/-!
---
title: Exponential bound for the raw intersection exception
type: definition and theorem
---
A fixed-size kernel certificate describes any large collection of common
primal images. The reference image cap and a joint density bound give an
explicit exceptional probability after paying the coefficient count.
-/

namespace Lax342547.RawIntersections

open Lax342547.MomentSpace Lax342547.RawFrames Lax342547.FrameSymmetry
open Lax342547.ProductImages Lax342547.TensorIntersections
open scoped ENNReal

variable {Comp B H N : Type} [Fintype Comp] [Fintype B] [Fintype H] [Fintype N]

def jointPlus {E : Matrix B B Binary} (o : Fin 2 → Comp → Frame B H N E) (e : Comp) :
    Matrix N (Fin 2 × (B ⊕ H)) Binary := jointMatrix (fun i => (plus (o i e)).val)

noncomputable def intersectionDimension {E : Matrix B B Binary}
    (o : Fin 2 → Comp → Frame B H N E) : ℕ :=
  ∑ e, Module.finrank Binary (intersectionSpace (o 0 e).P (o 1 e).P)

axiom intersection_kernel_bound {E : Matrix B B Binary}
    (o : Fin 2 → Comp → Frame B H N E) :
    intersectionDimension o ≤ ∑ e, Module.finrank Binary (LinearMap.ker (jointPlus o e).mulVecLin)

axiom reference_kernel_bound
    [DecidableEq Comp] [DecidableEq B] [DecidableEq H] [DecidableEq N]
    {E : Matrix B B Binary} [Nonempty (Frame B H N E)]
    (q : ℕ) (hq : 1 ≤ q)
    (hN : 2 * (Fintype.card B + Fintype.card H) + 1 ≤ Fintype.card N)
    (hp : (4 : ℝ) * (Fintype.card B + Fintype.card H : ℕ) ≤ (1 / 4 : ℝ) * Fintype.card N)
    (hc : (8 : ℝ) * Fintype.card Comp ≤ (1 / 4 : ℝ) * Fintype.card N) :
    (PMF.uniformOfFintype (Fin 2 → Comp → Frame B H N E)).toOuterMeasure
      {o | q ≤ intersectionDimension o} ≤
      (2 : ℝ≥0∞) ^ (Fintype.card Comp * (2 * (Fintype.card B + Fintype.card H)) * q) *
        (2 : ℝ≥0∞) ^ (-((3 / 4 : ℝ) * q * Fintype.card N))

axiom capped_intersection_bound
    [DecidableEq Comp] [DecidableEq B] [DecidableEq H] [DecidableEq N]
    {E : Matrix B B Binary} [Nonempty (Frame B H N E)]
    (D : ℕ) (hD : 1 ≤ D)
    (hN : 2 * (Fintype.card B + Fintype.card H) + 1 ≤ Fintype.card N)
    (hp : (4 : ℝ) * (Fintype.card B + Fintype.card H : ℕ) ≤ (1 / 4 : ℝ) * Fintype.card N)
    (hc : (8 : ℝ) * Fintype.card Comp ≤ (1 / 4 : ℝ) * Fintype.card N)
    (hcount : (Fintype.card Comp * (2 * (Fintype.card B + Fintype.card H)) * (2 * D) : ℕ) ≤
      (D : ℝ) * Fintype.card N / 4)
    (σ : PMF (Fin 2 → Comp → Frame B H N E))
    (hσ : ∀ o, σ o ≤ (2 : ℝ≥0∞) ^ (D * Fintype.card N) * PMF.uniformOfFintype _ o) :
    σ.toOuterMeasure {o | 2 * D < intersectionDimension o} ≤
      (2 : ℝ≥0∞) ^ (-((D : ℝ) * Fintype.card N / 4))

axiom exists_intersection_scale (a b c : ℕ) :
    ∃ M : ℕ, ∀ n : ℕ, 1 ≤ n →
      2 * (a * n + b) + 1 ≤ M * n ∧
      (4 : ℝ) * (a * n + b : ℕ) ≤ (1 / 4 : ℝ) * (M * n : ℕ) ∧
      (8 : ℝ) * c ≤ (1 / 4 : ℝ) * (M * n : ℕ) ∧
      ∀ D : ℕ, (c * (2 * (a * n + b)) * (2 * D) : ℕ) ≤ (D : ℝ) * (M * n : ℕ) / 4

axiom exists_paper_intersection_scale (pStar g h c : ℕ) :
    ∃ M : ℕ, ∀ n : ℕ, 1 ≤ n →
      2 * (pStar * (1 + (g * g + 3) * n) + h) + 1 ≤ M * n ∧
      (4 : ℝ) * (pStar * (1 + (g * g + 3) * n) + h : ℕ) ≤ (1 / 4 : ℝ) * (M * n : ℕ) ∧
      (8 : ℝ) * c ≤ (1 / 4 : ℝ) * (M * n : ℕ) ∧
      ∀ D : ℕ, (c * (2 * (pStar * (1 + (g * g + 3) * n) + h)) * (2 * D) : ℕ) ≤
        (D : ℝ) * (M * n : ℕ) / 4

end Lax342547.RawIntersections
