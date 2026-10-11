import Lax342547.SharpMixerLaw
import Lax342547Proofs.AtomDirections
import Lax342547.FiniteLinearLaw
import Lax342547.LowRankCounting
import Lax342547Proofs.ConcreteGeometry

namespace Lax342547Proofs.SharpMixerLaw

set_option backward.isDefEq.respectTransparency false

open Lax342547.SharpMixerLaw

theorem weighted_surjective {K A I : Type} [Field K] [Fintype A]
    (c : A → K) (hc : ∃ a, c a ≠ 0) : Function.Surjective (weighted (I := I) c) := by
  classical
  obtain ⟨a, ha⟩ := hc
  intro M
  refine ⟨Pi.single a ((c a)⁻¹ • M), ?_⟩
  simp [weighted, Pi.single_apply, smul_smul, ha]

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry Lax342547.AtomDirections
open scoped ENNReal

/--
---
conclusion: Lax342547.SharpMixerLaw.label_weighted_uniform
---
Distinct labels differ in some bit, so their coefficient sum at that bit
is nonzero in the binary field. The weighted matrix map is surjective.
-/
theorem label_weighted_uniform {b n : ℕ} (s t : Fin b → Binary) (hst : s ≠ t) :
    (PMF.uniformOfFintype (Fin b → Matrix (Fin n) (Fin n) Binary)).map
      (weighted (fun a => s a + t a)) = PMF.uniformOfFintype (Matrix (Fin n) (Fin n) Binary) := by
  apply Lax342547.FiniteLinearLaw.uniform_image_of_surjective
  apply weighted_surjective
  obtain ⟨a, ha⟩ : ∃ a, s a ≠ t a := Function.ne_iff.mp hst
  refine ⟨a, ?_⟩
  intro h
  apply ha
  calc
    s a = s a + (t a + t a) := by rw [ZModModule.add_self, add_zero]
    _ = (s a + t a) + t a := (add_assoc _ _ _).symm
    _ = t a := by rw [h, zero_add]

theorem sharp_injective {k n : ℕ} : Function.Injective (sharp (k := k) (n := n)) := by
  intro i j h
  simpa only [sharp, Sum.inr.injEq, Prod.mk.injEq, true_and] using h

theorem testerForm_sharp_directions {k n b degree r : ℕ} (hr : 2 * r ≤ n)
    (s t : Fin b → Binary) (u v : Fin n → Binary) :
    testerForm hr ((blockDirections (k := k) (degree := degree) s sharp).mulVec u)
      ((blockDirections t sharp).mulVec v) = 0 := by
  classical
  simp [testerForm, LinearMap.sum_apply, ConcreteGeometry.blockForm_apply,
    Matrix.mulVec, dotProduct, blockDirections, ordinary, shared, sharp]

theorem sharpForm_directions {k n b degree : ℕ} (hd : 1 ≤ degree)
    (M : Fin b → Matrix (Fin n) (Fin n) Binary) (s t : Fin b → Binary) (u v : Fin n → Binary) :
    sharpForm hd M ((blockDirections (k := k) s sharp).mulVec u) ((blockDirections t sharp).mulVec v) =
      ∑ a, (s a + t a) * (∑ i, ∑ j, u i * M a i j * v j) := by
  rw [ConcreteGeometry.sharpForm_apply]
  simp only [AtomDirections.blockDirections_mulVec _ sharp sharp_injective,
    ConcreteGeometry.eval_bit, ConcreteGeometry.eval_empty, one_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/--
---
conclusion: Lax342547.SharpMixerLaw.selfGram_sharp_block
---
The ordinary and shared testers vanish on sharp directions. Evaluating
the remaining form gives the selector sum s_a+t_a multiplying M_a.
Apply the bilinear form to basis vectors to recover the whole matrix block.
-/
theorem selfGram_sharp_block {k n b degree r : ℕ} (hr : 2 * r ≤ n) (hd : 1 ≤ degree)
    (M : Fin b → Matrix (Fin n) (Fin n) Binary) (s t : Fin b → Binary) :
    (blockDirections (k := k) (degree := degree) s sharp).transpose * selfGram hr hd M *
      blockDirections t sharp = weighted (fun a => s a + t a) M := by
  classical
  rw [selfGram, LinearMap.BilinForm.mul_toMatrix'_mul, Matrix.transpose_transpose]
  ext i j
  rw [LinearMap.BilinForm.toMatrix'_apply]
  change testerForm hr ((blockDirections s sharp).mulVec (Pi.single i 1))
      ((blockDirections t sharp).mulVec (Pi.single j 1)) +
    sharpForm hd M ((blockDirections s sharp).mulVec (Pi.single i 1))
      ((blockDirections t sharp).mulVec (Pi.single j 1)) = _
  rw [testerForm_sharp_directions, zero_add, sharpForm_directions]
  simp [weighted, Matrix.sum_apply, Matrix.smul_apply, Pi.single_apply, ite_mul, mul_ite]

/--
---
conclusion: Lax342547.SharpMixerLaw.selfGram_free_block
---
All tester and sharp coordinates vanish on a free Z-direction input.
Consequently an optional self-Gram evaluation contributes zero to the
free-direction block used to test a nonempty mixer parity.
-/
theorem selfGram_free_block {k n b degree r : ℕ} (hr : 2 * r ≤ n) (hd : 1 ≤ degree)
    (M : Fin b → Matrix (Fin n) (Fin n) Binary) (s t : Fin b → Binary) :
    (blockDirections (k := k) (degree := degree) s free).transpose * selfGram hr hd M *
      blockDirections t free = (0 : Matrix (Fin n) (Fin n) Binary) := by
  classical
  have ht (u v : Fin n → Binary) :
      testerForm hr ((blockDirections (k := k) (degree := degree) s free).mulVec u)
        ((blockDirections t free).mulVec v) = 0 := by
    simp [testerForm, LinearMap.sum_apply, ConcreteGeometry.blockForm_apply,
      Matrix.mulVec, dotProduct, blockDirections, ordinary, shared, free]
  have hs (u v : Fin n → Binary) :
      sharpForm hd M ((blockDirections (k := k) s free).mulVec u)
        ((blockDirections t free).mulVec v) = 0 := by
    simp [ConcreteGeometry.sharpForm_apply, Matrix.mulVec, dotProduct, blockDirections, sharp, free]
  rw [selfGram, LinearMap.BilinForm.mul_toMatrix'_mul, Matrix.transpose_transpose]
  ext i j
  rw [LinearMap.BilinForm.toMatrix'_apply]
  change testerForm hr ((blockDirections s free).mulVec (Pi.single i 1))
      ((blockDirections t free).mulVec (Pi.single j 1)) +
    sharpForm hd M ((blockDirections s free).mulVec (Pi.single i 1))
      ((blockDirections t free).mulVec (Pi.single j 1)) = _
  rw [ht, hs, add_zero]
  rfl

theorem alternatingBlock_surjective {K I N P : Type} [Field K] [Fintype N] [Fintype P]
    (c : N → I) (d : P → I) (hc : Function.Injective c) (hd : Function.Injective d)
    (hcd : ∀ i j, c i ≠ d j) : Function.Surjective (alternatingBlock (K := K) c d) := by
  classical
  intro B
  let M : Matrix I I K := fun i j => ∑ a : N, ∑ b : P, if c a = i ∧ d b = j then B a b else 0
  have hf (a : N) (b : P) : M (c a) (d b) = B a b := by
    simp [M, hc.eq_iff, hd.eq_iff, ite_and]
  have hr (a : N) (b : P) : M (d b) (c a) = 0 := by
    simp [M, hcd]
  refine ⟨M, ?_⟩
  ext a b
  change M (c a) (d b) + M (d b) (c a) = B a b
  rw [hf, hr, add_zero]

/--
---
conclusion: Lax342547.SharpMixerLaw.alternating_block_uniform
---
Prescribe the chosen forward block and set its reverse to zero. Disjoint
index sets make these prescriptions consistent, so the alternating-block
observation is a surjective linear map and hence has the uniform law.
-/
theorem alternating_block_uniform {I N P : Type} [Fintype I] [Fintype N] [Fintype P]
    [DecidableEq I] [DecidableEq N] [DecidableEq P]
    (c : N → I) (d : P → I) (hc : Function.Injective c) (hd : Function.Injective d)
    (hcd : ∀ i j, c i ≠ d j) :
    (PMF.uniformOfFintype (Matrix I I Binary)).map (alternatingBlock c d) =
      PMF.uniformOfFintype (Matrix N P Binary) :=
  Lax342547.FiniteLinearLaw.uniform_image_of_surjective _ (alternatingBlock_surjective c d hc hd hcd)

theorem alternating_rank_bound {I N P : Type} [Fintype I] [Fintype N] [Fintype P]
    [DecidableEq I] [DecidableEq N] [DecidableEq P]
    (c : N → I) (d : P → I) (hc : Function.Injective c) (hd : Function.Injective d)
    (hcd : ∀ i j, c i ≠ d j) (r : ℕ) :
    (PMF.uniformOfFintype (Matrix I I Binary)).toOuterMeasure {M | (M + M.transpose).rank ≤ r} ≤
      (2 : ℝ≥0∞) ^ ((Fintype.card N + Fintype.card P) * r) / 2 ^ (Fintype.card N * Fintype.card P) := by
  calc
    _ ≤ (PMF.uniformOfFintype (Matrix I I Binary)).toOuterMeasure
        ((alternatingBlock c d) ⁻¹' {B | B.rank ≤ r}) := by
      apply MeasureTheory.OuterMeasure.mono
      intro M hM
      exact (Matrix.rank_submatrix_le (M + M.transpose) c d).trans hM
    _ = ((PMF.uniformOfFintype (Matrix I I Binary)).map (alternatingBlock c d)).toOuterMeasure
        {B | B.rank ≤ r} := (PMF.toOuterMeasure_map_apply _ _ _).symm
    _ = (PMF.uniformOfFintype (Matrix N P Binary)).toOuterMeasure {B | B.rank ≤ r} := by
      rw [Lax342547.SharpMixerLaw.alternating_block_uniform c d hc hd hcd]
    _ ≤ _ := Lax342547.LowRankCounting.uniform_low_rank_bound r

/--
---
conclusion: Lax342547.SharpMixerLaw.alternating_low_rank_bound
---
Use the disjoint even and odd indices for a square block of side floor(n/2).
Its rank cannot exceed the rank of the alternating matrix, and its uniform
law satisfies the rectangular low-rank probability bound.
-/
theorem alternating_low_rank_bound (n r : ℕ) :
    (PMF.uniformOfFintype (Matrix (Fin n) (Fin n) Binary)).toOuterMeasure
      {M | (M + M.transpose).rank ≤ r} ≤
        (2 : ℝ≥0∞) ^ ((n / 2 + n / 2) * r) / 2 ^ ((n / 2) * (n / 2)) := by
  have hn : 2 * (n / 2) ≤ n := by omega
  have hl : Function.Injective (pairLeft hn) := by
    intro i j h
    apply Fin.ext
    have h' := congrArg Fin.val h
    simp only [pairLeft] at h'
    omega
  have hr : Function.Injective (pairRight hn) := by
    intro i j h
    apply Fin.ext
    have h' := congrArg Fin.val h
    simp only [pairRight] at h'
    omega
  have hd (i j : Fin (n / 2)) : pairLeft hn i ≠ pairRight hn j := by
    intro h
    have h' := congrArg Fin.val h
    simp only [pairLeft, pairRight] at h'
    omega
  simpa only [Fintype.card_fin] using alternating_rank_bound (pairLeft hn) (pairRight hn) hl hr hd r

/--
---
conclusion: Lax342547.SharpMixerLaw.label_parity_low_rank_bounds
---
Push the uniform family of sharp mixers through its nonzero label-weighted
sum. The forward and reverse ranks obey the square-matrix count; their
alternating sum obeys the disjoint-block count proved above.
-/
theorem label_parity_low_rank_bounds {b n : ℕ} (s t : Fin b → Binary) (hst : s ≠ t) (r : ℕ) :
    let A := weighted (I := Fin n) (fun a => s a + t a)
    let μ := PMF.uniformOfFintype (Fin b → Matrix (Fin n) (Fin n) Binary)
    μ.toOuterMeasure {M | (A M).rank ≤ r} ≤ (2 : ℝ≥0∞) ^ ((n + n) * r) / 2 ^ (n * n) ∧
    μ.toOuterMeasure {M | (A M).transpose.rank ≤ r} ≤ (2 : ℝ≥0∞) ^ ((n + n) * r) / 2 ^ (n * n) ∧
    μ.toOuterMeasure {M | (A M + (A M).transpose).rank ≤ r} ≤
      (2 : ℝ≥0∞) ^ ((n / 2 + n / 2) * r) / 2 ^ ((n / 2) * (n / 2)) := by
  dsimp only
  have hu := Lax342547.SharpMixerLaw.label_weighted_uniform (n := n) s t hst
  have hforward := Lax342547.LowRankCounting.uniform_low_rank_bound (I := Fin n) (J := Fin n) r
  rw [← hu, PMF.toOuterMeasure_map_apply] at hforward
  simp only [Fintype.card_fin, Set.preimage_ofPred_eq] at hforward
  refine ⟨hforward, ?_, ?_⟩
  · simpa only [Matrix.rank_transpose] using hforward
  · have h := Lax342547.SharpMixerLaw.alternating_low_rank_bound n r
    rw [← hu, PMF.toOuterMeasure_map_apply] at h
    exact h

end Lax342547Proofs.SharpMixerLaw
