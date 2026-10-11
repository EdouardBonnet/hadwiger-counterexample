import Lax342547.GramNormalization
import Lax342547Proofs.GramColumns
import Lax342547Proofs.FiniteProbability
import Lax342547.CorankCounting
import Lax342547.GramColumns
import Lax342547Proofs.FiniteUniform

namespace Lax342547Proofs.GramNormalization

open Lax342547.MomentSpace Lax342547.GramColumns Lax342547.GramNormalization
open scoped ENNReal

theorem noninjective_iff {J N : Type} [Fintype J] [Fintype N] (M : Matrix N J Binary) :
    ¬ Function.Injective M.mulVec ↔ M.rank + 1 ≤ Fintype.card J := by
  have hd := M.mulVecLin.finrank_range_add_finrank_ker
  change M.rank + Module.finrank Binary (LinearMap.ker M.mulVecLin) =
    Module.finrank Binary (J → Binary) at hd
  rw [Module.finrank_fintype_fun_eq_card] at hd
  have hi : Function.Injective M.mulVec ↔ Module.finrank Binary (LinearMap.ker M.mulVecLin) = 0 := by
    rw [Submodule.finrank_eq_zero, LinearMap.ker_eq_bot]
    rfl
  rw [hi]
  omega

/--
---
conclusion: Lax342547.GramNormalization.column_failure
---
Failure of column injectivity is positive row corank of the transpose.
Transpose preserves the uniform matrix law, so the checked one-relation
corank bound gives 2^(number of columns - ambient dimension).
-/
theorem column_failure {J N : Type} [Fintype J] [Fintype N] [DecidableEq J] [DecidableEq N] :
    (PMF.uniformOfFintype (Matrix N J Binary)).toOuterMeasure {A | ¬ Function.Injective A.mulVec} ≤
      (2 : ℝ≥0∞) ^ Fintype.card J / 2 ^ Fintype.card N := by
  let e : Matrix N J Binary ≃ Matrix J N Binary :=
    ⟨Matrix.transpose, Matrix.transpose, Matrix.transpose_transpose, Matrix.transpose_transpose⟩
  have h := Lax342547.CorankCounting.uniform_corank_bound (I := J) (J := N) 1
  rw [← FiniteUniform.map_equiv e, PMF.toOuterMeasure_map_apply] at h
  have hs : e ⁻¹' {M | M.rank + 1 ≤ Fintype.card J} =
      {M | ¬ Function.Injective M.mulVec} := by
    ext M
    change M.transpose.rank + 1 ≤ Fintype.card J ↔ ¬ Function.Injective M.mulVec
    rw [Matrix.rank_transpose, noninjective_iff]
  simpa only [hs, one_mul] using h

variable {I J N : Type} [Fintype I] [Fintype J] [Fintype N]
  [DecidableEq I] [DecidableEq J] [DecidableEq N]

theorem slice_lower (A : Matrix N I Binary) (hA : Function.Injective A.mulVec)
    (G : Matrix I J Binary) :
    (1 / (2 : ℝ≥0∞) ^ (Fintype.card I * Fintype.card J)) *
      (1 - (2 : ℝ≥0∞) ^ (Fintype.card I + Fintype.card J) / 2 ^ Fintype.card N) ≤
    (PMF.uniformOfFintype (Matrix N J Binary)).toOuterMeasure
      {B | Function.Injective B.mulVec ∧ A.transpose * B = G} := by
  classical
  obtain ⟨B₀, h₀⟩ := GramColumns.gram_surjective A hA G
  let : Nonempty (GramFiber A G) := ⟨⟨B₀, h₀⟩⟩
  let p := PMF.uniformOfFintype (GramFiber A G)
  have hb : p.toOuterMeasure {B | Function.Injective B.val.mulVec}ᶜ ≤
      (2 : ℝ≥0∞) ^ (Fintype.card I + Fintype.card J) / 2 ^ Fintype.card N :=
    Lax342547.GramColumns.conditional_failure A hA G
  have hl := FiniteProbability.event_ge_of_compl_le p {B | Function.Injective B.val.mulVec} _ hb
  have he := @FiniteProbability.uniform_subtype_event (Matrix N J Binary) inferInstance inferInstance
    {B | A.transpose * B = G} {B | Function.Injective B.mulVec}
    (inferInstance : Fintype (GramFiber A G)) (inferInstance : Nonempty (GramFiber A G))
  rw [Lax342547.GramColumns.gram_probability A hA G] at he
  have hs : {B : Matrix N J Binary | Function.Injective B.mulVec ∧ A.transpose * B = G} =
      {B | A.transpose * B = G} ∩ {B | Function.Injective B.mulVec} := by
    ext B
    exact and_comm
  rw [hs, he]
  gcongr
  exact hl

/--
---
conclusion: Lax342547.GramNormalization.normalization_upper
---
Expose the plus matrix. On every injective plus frame, the Gram event
costs exactly 2^(-pq); requiring minus injectivity can only decrease its
probability. The noninjective plus slices contribute zero.
-/
theorem normalization_upper (G : Matrix I J Binary) :
    probability (N := N) G ≤ 1 / (2 : ℝ≥0∞) ^ (Fintype.card I * Fintype.card J) := by
  classical
  let c : ℝ≥0∞ := 1 / 2 ^ (Fintype.card I * Fintype.card J)
  let p := PMF.uniformOfFintype (Matrix N I Binary)
  have hsum : ∑ A, p A = 1 := by simpa only [tsum_fintype] using p.tsum_coe
  rw [probability, FiniteProbability.uniform_product_event]
  calc
    _ ≤ ∑ A : Matrix N I Binary, p A * c := by
      apply Finset.sum_le_sum
      intro A _
      have hs : (PMF.uniformOfFintype (Matrix N J Binary)).toOuterMeasure
          {B | Function.Injective A.mulVec ∧ Function.Injective B.mulVec ∧ A.transpose * B = G} ≤ c := by
        by_cases hA : Function.Injective A.mulVec
        · calc
            _ ≤ (PMF.uniformOfFintype (Matrix N J Binary)).toOuterMeasure
                {B | A.transpose * B = G} :=
              (PMF.uniformOfFintype _).toOuterMeasure.mono (fun _ h => h.2.2)
            _ = c := Lax342547.GramColumns.gram_probability A hA G
        · simp [hA]
      exact mul_le_mul_of_nonneg_left hs zero_le
    _ = c := by rw [← Finset.sum_mul, hsum, one_mul]

/--
---
conclusion: Lax342547.GramNormalization.normalization_lower
---
The plus frame is injective with mass at least 1-2^(p-N). On each such
slice, the exact Gram factor is 2^(-pq), and the remaining minus-frame
injectivity costs at most 2^(p+q-N). Finite product-law integration
multiplies these three explicit lower bounds.
-/
theorem normalization_lower (G : Matrix I J Binary) :
    (1 / (2 : ℝ≥0∞) ^ (Fintype.card I * Fintype.card J)) *
      (1 - (2 : ℝ≥0∞) ^ Fintype.card I / 2 ^ Fintype.card N) *
      (1 - (2 : ℝ≥0∞) ^ (Fintype.card I + Fintype.card J) / 2 ^ Fintype.card N) ≤
        probability (N := N) G := by
  classical
  let c : ℝ≥0∞ := 1 / 2 ^ (Fintype.card I * Fintype.card J)
  let ε₁ : ℝ≥0∞ := 2 ^ Fintype.card I / 2 ^ Fintype.card N
  let ε₂ : ℝ≥0∞ := 2 ^ (Fintype.card I + Fintype.card J) / 2 ^ Fintype.card N
  let p := PMF.uniformOfFintype (Matrix N I Binary)
  let good := {A : Matrix N I Binary | Function.Injective A.mulVec}
  have hp : 1 - ε₁ ≤ p.toOuterMeasure good :=
    FiniteProbability.event_ge_of_compl_le p good ε₁ (Lax342547.GramNormalization.column_failure (J := I) (N := N))
  have hl : p.toOuterMeasure good * (c * (1 - ε₂)) ≤ probability (N := N) G := by
    rw [PMF.toOuterMeasure_apply_fintype, Finset.sum_mul, probability,
      FiniteProbability.uniform_product_event]
    apply Finset.sum_le_sum
    intro A _
    by_cases hA : Function.Injective A.mulVec
    · rw [Set.indicator_of_mem hA]
      have hs := slice_lower A hA G
      change p A * (c * (1 - ε₂)) ≤ p A *
        (PMF.uniformOfFintype (Matrix N J Binary)).toOuterMeasure
          {B | Function.Injective A.mulVec ∧ Function.Injective B.mulVec ∧ A.transpose * B = G}
      have he : {B : Matrix N J Binary |
          Function.Injective A.mulVec ∧ Function.Injective B.mulVec ∧ A.transpose * B = G} =
          {B | Function.Injective B.mulVec ∧ A.transpose * B = G} := by
        ext B
        simp only [hA, true_and, Set.mem_ofPred_eq]
      rw [he]
      exact mul_le_mul_of_nonneg_left hs zero_le
    · have hn : A ∉ good := hA
      simp [Set.indicator_of_notMem hn]
  change c * (1 - ε₁) * (1 - ε₂) ≤ _
  calc
    _ = (1 - ε₁) * (c * (1 - ε₂)) := by ac_rfl
    _ ≤ p.toOuterMeasure good * (c * (1 - ε₂)) := mul_le_mul_of_nonneg_right hp zero_le
    _ ≤ _ := hl

omit [Fintype I] [Fintype J] [Fintype N] [DecidableEq I] [DecidableEq J] [DecidableEq N] in
theorem power_ratio_le_half (a b : ℕ) (h : a + 1 ≤ b) :
    (2 : ℝ≥0∞) ^ a / 2 ^ b ≤ 1 / 2 := by
  calc
    _ ≤ (2 : ℝ≥0∞) ^ a / 2 ^ (a + 1) :=
      ENNReal.div_le_div_left (pow_le_pow_right₀ (by norm_num) h) _
    _ = _ := by
      rw [pow_succ]
      simpa only [mul_one] using ENNReal.mul_div_mul_left 1 2
        (show (2 : ℝ≥0∞) ^ a ≠ 0 by simp) (by simp)

/--
---
conclusion: Lax342547.GramNormalization.normalization_quarter
---
One extra ambient dimension beyond p+q makes both failure bounds at most
one half. Hence every individually injective Gram orbit has independent
column probability at least 2^(-pq-2), the explicit density denominator
used for bounded channel frames.
-/
theorem normalization_quarter (G : Matrix I J Binary)
    (hN : Fintype.card I + Fintype.card J + 1 ≤ Fintype.card N) :
    1 / (2 : ℝ≥0∞) ^ (Fintype.card I * Fintype.card J + 2) ≤ probability (N := N) G := by
  have h₁ := power_ratio_le_half (Fintype.card I) (Fintype.card N) (by omega)
  have h₂ := power_ratio_le_half (Fintype.card I + Fintype.card J) (Fintype.card N) hN
  have hh : 1 - (1 / 2 : ℝ≥0∞) = 1 / 2 := by norm_num
  have l₁ : (1 / 2 : ℝ≥0∞) ≤ 1 - (2 : ℝ≥0∞) ^ Fintype.card I / 2 ^ Fintype.card N := by
    rw [← hh]
    exact tsub_le_tsub_left h₁ _
  have l₂ : (1 / 2 : ℝ≥0∞) ≤
      1 - (2 : ℝ≥0∞) ^ (Fintype.card I + Fintype.card J) / 2 ^ Fintype.card N := by
    rw [← hh]
    exact tsub_le_tsub_left h₂ _
  calc
    _ = (1 / (2 : ℝ≥0∞) ^ (Fintype.card I * Fintype.card J)) * (1 / 2) * (1 / 2) := by
      simp [pow_add, pow_two, one_div, ENNReal.mul_inv, mul_assoc]
    _ ≤ (1 / (2 : ℝ≥0∞) ^ (Fintype.card I * Fintype.card J)) *
        (1 - (2 : ℝ≥0∞) ^ Fintype.card I / 2 ^ Fintype.card N) *
        (1 - (2 : ℝ≥0∞) ^ (Fintype.card I + Fintype.card J) / 2 ^ Fintype.card N) := by
      gcongr
    _ ≤ _ := Lax342547.GramNormalization.normalization_lower G

end Lax342547Proofs.GramNormalization
