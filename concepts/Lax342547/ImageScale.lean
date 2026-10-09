import Lax342547.ReferenceImages
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
---
title: Paying the reference-image conditioning and dimension costs
type: theorem
---
The finite two-endpoint cap has prefactor 16 per component and loses
2(d+h) dimensions on minus images. Both costs are paid uniformly over
every positive total rank by choosing the ambient scale sufficiently
large. A single scale works for every positive n and every tested rank.
-/

namespace Lax342547.ImageScale

open Lax342547.MomentSpace Lax342547.RawFrames Lax342547.ReferenceImages
open scoped ENNReal

axiom cost_bound (c p N a b : ℕ) (ε : ℝ) (hε : 0 < ε)
    (hN : 2 * p ≤ N) (ht : 1 ≤ a + b)
    (hp : (4 : ℝ) * p ≤ ε * N) (hc : (8 : ℝ) * c ≤ ε * N) :
    (4 : ℝ≥0∞) ^ (2 * c) / 2 ^ (N * a + (N - 2 * p) * b) ≤
      (2 : ℝ≥0∞) ^ (-((1 - ε) * (a + b : ℕ) * N))

axiom exists_scale (a b c : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℕ, ∀ n : ℕ, 1 ≤ n →
      2 * (a * n + b) + 1 ≤ M * n ∧
      (4 : ℝ) * (a * n + b : ℕ) ≤ ε * (M * n : ℕ) ∧
      (8 : ℝ) * c ≤ ε * (M * n : ℕ)

axiom exists_paper_scale (pStar g h c : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℕ, ∀ n : ℕ, 1 ≤ n →
      2 * (pStar * (1 + (g * g + 3) * n) + h) + 1 ≤ M * n ∧
      (4 : ℝ) * (pStar * (1 + (g * g + 3) * n) + h : ℕ) ≤ ε * (M * n : ℕ) ∧
      (8 : ℝ) * c ≤ ε * (M * n : ℕ)

axiom reference_image_cap {Comp B H N : Type}
    [Fintype Comp] [Fintype B] [Fintype H] [Fintype N]
    [DecidableEq Comp] [DecidableEq B] [DecidableEq H] [DecidableEq N]
    {K L : Comp → Type} [∀ e, Fintype (K e)] [∀ e, Fintype (L e)]
    {E : Matrix B B Binary} [Nonempty (Frame B H N E)]
    (ε : ℝ) (hε : 0 < ε)
    (hN : 2 * (Fintype.card B + Fintype.card H) + 1 ≤ Fintype.card N)
    (hp : (4 : ℝ) * (Fintype.card B + Fintype.card H : ℕ) ≤ ε * Fintype.card N)
    (hc : (8 : ℝ) * Fintype.card Comp ≤ ε * Fintype.card N)
    (C : ∀ e, Matrix (Fin 2 × (B ⊕ H)) (K e) Binary)
    (D : ∀ e, Matrix (Fin 2 × (B ⊕ H)) (L e) Binary)
    (y : ∀ e, Matrix N (K e) Binary) (z : ∀ e, Matrix N (L e) Binary)
    (ht : 1 ≤ (∑ e, (C e).rank) + ∑ e, (D e).rank) :
    (PMF.uniformOfFintype (Fin 2 → Comp → Frame B H N E)).toOuterMeasure
      {o | ∀ e, plusImages (C e) (fun i => o i e) = y e ∧ minusImages (D e) (fun i => o i e) = z e} ≤
      (2 : ℝ≥0∞) ^ (-((1 - ε) * ((∑ e, (C e).rank) + ∑ e, (D e).rank : ℕ) * Fintype.card N))

end Lax342547.ImageScale
