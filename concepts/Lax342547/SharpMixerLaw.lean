import Lax342547.AtomDirections
import Lax342547.FiniteLinearLaw
import Lax342547.LowRankCounting

/-!
---
title: Random sharp-block forms and their alternating parity
type: definition and theorem
---
The sharp part of the self-Gram form at distinct labels is a nonzero
linear combination of independently uniform matrices. It is uniform.
Although its sum with its transpose is alternating, any block on disjoint
row and column index sets is uniform and supplies the required rank bound.
-/

namespace Lax342547.SharpMixerLaw

variable {K A I N P : Type} [Field K] [Fintype A]

def weighted (c : A → K) : (A → Matrix I I K) →ₗ[K] Matrix I I K where
  toFun M := ∑ a, c a • M a
  map_add' M L := by simp [smul_add, Finset.sum_add_distrib]
  map_smul' r M := by simp [smul_smul, Finset.smul_sum, mul_comm]

def alternatingBlock (c : N → I) (d : P → I) : Matrix I I K →ₗ[K] Matrix N P K where
  toFun M i j := M (c i) (d j) + M (d j) (c i)
  map_add' M L := by
    ext i j
    change (M (c i) (d j) + L (c i) (d j)) + (M (d j) (c i) + L (d j) (c i)) =
      (M (c i) (d j) + M (d j) (c i)) + (L (c i) (d j) + L (d j) (c i))
    exact add_add_add_comm _ _ _ _
  map_smul' a M := by
    ext i j
    change a * M (c i) (d j) + a * M (d j) (c i) = a * (M (c i) (d j) + M (d j) (c i))
    exact (mul_add _ _ _).symm

open Lax342547.MomentSpace Lax342547.ConcreteGeometry Lax342547.AtomDirections
open scoped ENNReal

axiom label_weighted_uniform {b n : ℕ} (s t : Fin b → Binary) (hst : s ≠ t) :
    (PMF.uniformOfFintype (Fin b → Matrix (Fin n) (Fin n) Binary)).map
      (weighted (fun a => s a + t a)) = PMF.uniformOfFintype (Matrix (Fin n) (Fin n) Binary)

axiom selfGram_sharp_block {k n b degree r : ℕ} (hr : 2 * r ≤ n) (hd : 1 ≤ degree)
    (M : Fin b → Matrix (Fin n) (Fin n) Binary) (s t : Fin b → Binary) :
    (blockDirections (k := k) (degree := degree) s sharp).transpose * selfGram hr hd M *
      blockDirections t sharp = weighted (fun a => s a + t a) M

axiom selfGram_free_block {k n b degree r : ℕ} (hr : 2 * r ≤ n) (hd : 1 ≤ degree)
    (M : Fin b → Matrix (Fin n) (Fin n) Binary) (s t : Fin b → Binary) :
    (blockDirections (k := k) (degree := degree) s free).transpose * selfGram hr hd M *
      blockDirections t free = (0 : Matrix (Fin n) (Fin n) Binary)

axiom alternating_block_uniform {I N P : Type} [Fintype I] [Fintype N] [Fintype P]
    [DecidableEq I] [DecidableEq N] [DecidableEq P]
    (c : N → I) (d : P → I) (hc : Function.Injective c) (hd : Function.Injective d)
    (hcd : ∀ i j, c i ≠ d j) :
    (PMF.uniformOfFintype (Matrix I I Binary)).map (alternatingBlock c d) =
      PMF.uniformOfFintype (Matrix N P Binary)

axiom alternating_low_rank_bound (n r : ℕ) :
    (PMF.uniformOfFintype (Matrix (Fin n) (Fin n) Binary)).toOuterMeasure
      {M | (M + M.transpose).rank ≤ r} ≤
        (2 : ℝ≥0∞) ^ ((n / 2 + n / 2) * r) / 2 ^ ((n / 2) * (n / 2))

axiom label_parity_low_rank_bounds {b n : ℕ} (s t : Fin b → Binary) (hst : s ≠ t) (r : ℕ) :
    let A := weighted (I := Fin n) (fun a => s a + t a)
    let μ := PMF.uniformOfFintype (Fin b → Matrix (Fin n) (Fin n) Binary)
    μ.toOuterMeasure {M | (A M).rank ≤ r} ≤ (2 : ℝ≥0∞) ^ ((n + n) * r) / 2 ^ (n * n) ∧
    μ.toOuterMeasure {M | (A M).transpose.rank ≤ r} ≤ (2 : ℝ≥0∞) ^ ((n + n) * r) / 2 ^ (n * n) ∧
    μ.toOuterMeasure {M | (A M + (A M).transpose).rank ≤ r} ≤
      (2 : ℝ≥0∞) ^ ((n / 2 + n / 2) * r) / 2 ^ ((n / 2) * (n / 2))

end Lax342547.SharpMixerLaw
