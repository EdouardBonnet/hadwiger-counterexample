import Lax342547.HistogramGram
import Lax342547Proofs.GramNormalization

namespace Lax342547Proofs.HistogramGram

open Lax342547.MomentSpace Lax342547.HistogramGram
open scoped BigOperators ENNReal

theorem probability_finite {I J N : Type} [Fintype I] [Fintype J] [Fintype N]
    [DecidableEq I] [DecidableEq J] [DecidableEq N] (G : Matrix I J Binary) :
    Lax342547.GramNormalization.probability (N := N) G ≠ ⊤ :=
  ne_top_of_le_ne_top (by simp) (Lax342547Proofs.GramNormalization.normalization_upper G)

/--
---
conclusion: Lax342547.HistogramGram.normalized_bounds
---
-/
theorem normalized_bounds {I J N : Type} [Fintype I] [Fintype J] [Fintype N]
    [DecidableEq I] [DecidableEq J] [DecidableEq N] (G : Matrix I J Binary)
    (hN : Fintype.card I+Fintype.card J ≤ Fintype.card N) :
    0 ≤ normalized (N := N) G ∧ normalized (N := N) G ≤ 1 ∧
      1-2*((2 : ℝ)^(Fintype.card I+Fintype.card J)/(2 : ℝ)^Fintype.card N) ≤ normalized (N := N) G := by
  have hupper := ENNReal.toReal_mono (by simp)
    (Lax342547Proofs.GramNormalization.normalization_upper (N := N) G)
  simp only [ENNReal.toReal_div,ENNReal.toReal_one,ENNReal.toReal_pow,ENNReal.toReal_ofNat] at hupper
  have hlower := ENNReal.toReal_mono (probability_finite (N := N) G)
    (Lax342547Proofs.GramNormalization.normalization_lower (N := N) G)
  have h₁ : (2 : ℝ≥0∞)^Fintype.card I/(2 : ℝ≥0∞)^Fintype.card N ≤ 1 := by
    apply (ENNReal.div_le_iff (by simp) (by simp)).mpr
    simpa only [one_mul] using pow_le_pow_right₀ (by norm_num : (1 : ℝ≥0∞) ≤ 2) (by omega : Fintype.card I ≤ Fintype.card N)
  have h₂ : (2 : ℝ≥0∞)^(Fintype.card I+Fintype.card J)/(2 : ℝ≥0∞)^Fintype.card N ≤ 1 := by
    apply (ENNReal.div_le_iff (by simp) (by simp)).mpr
    simpa only [one_mul] using pow_le_pow_right₀ (by norm_num : (1 : ℝ≥0∞) ≤ 2) hN
  rw [ENNReal.toReal_mul,ENNReal.toReal_mul,
    ENNReal.toReal_sub_of_le h₁ (by simp),ENNReal.toReal_sub_of_le h₂ (by simp)] at hlower
  simp only [ENNReal.toReal_div,ENNReal.toReal_one,ENNReal.toReal_pow,ENNReal.toReal_ofNat] at hlower
  have hp : 0 < (2 : ℝ)^(Fintype.card I*Fintype.card J) := by positivity
  have hε : (2 : ℝ)^Fintype.card I/(2 : ℝ)^Fintype.card N ≤
      (2 : ℝ)^(Fintype.card I+Fintype.card J)/(2 : ℝ)^Fintype.card N := by
    gcongr
    · norm_num
    · omega
  have hε₁ : 0 ≤ (2 : ℝ)^Fintype.card I/(2 : ℝ)^Fintype.card N := by positivity
  have hε₂ : 0 ≤ (2 : ℝ)^(Fintype.card I+Fintype.card J)/(2 : ℝ)^Fintype.card N := by positivity
  have hL := mul_le_mul_of_nonneg_left hlower hp.le
  have hU := mul_le_mul_of_nonneg_left hupper hp.le
  have hc : (2 : ℝ)^(Fintype.card I*Fintype.card J)*(1/(2 : ℝ)^(Fintype.card I*Fintype.card J)) = 1 := by field_simp
  simp only [← mul_assoc] at hL
  rw [hc,one_mul] at hL
  rw [hc] at hU
  exact ⟨by unfold normalized; positivity,hU,by unfold normalized; nlinarith⟩

/--
---
conclusion: Lax342547.HistogramGram.normalized_error
---
-/
theorem normalized_error {I J N : Type} [Fintype I] [Fintype J] [Fintype N]
    [DecidableEq I] [DecidableEq J] [DecidableEq N] (G : Matrix I J Binary)
    (hN : Fintype.card I+Fintype.card J ≤ Fintype.card N) :
    |normalized (N := N) G-1| ≤
      2*((2 : ℝ)^(Fintype.card I+Fintype.card J)/(2 : ℝ)^Fintype.card N) := by
  obtain ⟨_,hu,hl⟩ := normalized_bounds (N := N) G hN
  rw [abs_of_nonpos (by linarith : normalized (N := N) G-1 ≤ 0)]
  linarith

/--
---
conclusion: Lax342547.HistogramGram.product_error
---
-/
theorem product_error {D : Type} (S : Finset D) (q ε : D → ℝ)
    (hq : ∀ d ∈ S,0 ≤ q d ∧ q d ≤ 1) (hε : ∀ d ∈ S,0 ≤ ε d)
    (herr : ∀ d ∈ S,1-ε d ≤ q d) :
    |(∏ d ∈ S,q d)-1| ≤ ∑ d ∈ S,ε d := by
  classical
  have hbounds : 0 ≤ ∏ d ∈ S,q d ∧ (∏ d ∈ S,q d) ≤ 1 ∧
      1-(∑ d ∈ S,ε d) ≤ ∏ d ∈ S,q d := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert a S ha ih =>
      have hi := ih (fun d hd => hq d (Finset.mem_insert_of_mem hd))
        (fun d hd => hε d (Finset.mem_insert_of_mem hd))
        (fun d hd => herr d (Finset.mem_insert_of_mem hd))
      obtain ⟨ha0,ha1⟩ := hq a (Finset.mem_insert_self _ _)
      have hea := hε a (Finset.mem_insert_self _ _)
      have hla := herr a (Finset.mem_insert_self _ _)
      simp only [Finset.prod_insert ha,Finset.sum_insert ha]
      refine ⟨mul_nonneg ha0 hi.1,(mul_le_mul ha1 hi.2.1 hi.1 (by norm_num)).trans_eq (one_mul 1),?_⟩
      have hs : 0 ≤ ∑ d ∈ S,ε d := Finset.sum_nonneg (fun d hd => hε d (Finset.mem_insert_of_mem hd))
      nlinarith
  rw [abs_of_nonpos (by linarith [hbounds.2.1] : (∏ d ∈ S,q d)-1 ≤ 0)]
  linarith [hbounds.2.2]

/--
---
conclusion: Lax342547.HistogramGram.independent_groups_error
---
The relative normalization error adds over heterogeneous groups.
-/
theorem independent_groups_error {S N : Type} [Fintype S] [Fintype N] [DecidableEq N]
    {I J : S → Type} [∀ s,Fintype (I s)] [∀ s,Fintype (J s)]
    [∀ s,DecidableEq (I s)] [∀ s,DecidableEq (J s)]
    (G : ∀ s,Matrix (I s) (J s) Binary)
    (hN : ∀ s,Fintype.card (I s)+Fintype.card (J s) ≤ Fintype.card N) :
    |(∏ s,normalized (N := N) (G s))-1| ≤
      ∑ s,2*((2 : ℝ)^(Fintype.card (I s)+Fintype.card (J s))/(2 : ℝ)^Fintype.card N) := by
  apply product_error
  · intro s _
    exact ⟨(normalized_bounds (G s) (hN s)).1,(normalized_bounds (G s) (hN s)).2.1⟩
  · intro s _; positivity
  · intro s _
    exact (normalized_bounds (G s) (hN s)).2.2

/--
---
conclusion: Lax342547.HistogramGram.half_ambient_error
---
-/
theorem half_ambient_error {I J N : Type} [Fintype I] [Fintype J] [Fintype N]
    [DecidableEq I] [DecidableEq J] [DecidableEq N] (G : Matrix I J Binary)
    (hN : Fintype.card I+Fintype.card J ≤ Fintype.card N/2) :
    |normalized (N := N) G-1| ≤ 2/(2 : ℝ)^(Fintype.card N/2) := by
  have hh := normalized_error G (by omega : Fintype.card I+Fintype.card J ≤ Fintype.card N)
  refine hh.trans ?_
  have hp : (2 : ℝ)^(Fintype.card I+Fintype.card J)*(2 : ℝ)^(Fintype.card N/2) ≤
      (2 : ℝ)^Fintype.card N := by
    rw [← pow_add]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hden : 0 < (2 : ℝ)^Fintype.card N := by positivity
  have hhalf : 0 < (2 : ℝ)^(Fintype.card N/2) := by positivity
  have hr : (2 : ℝ)^(Fintype.card I+Fintype.card J)/(2 : ℝ)^Fintype.card N ≤
      1/(2 : ℝ)^(Fintype.card N/2) := (div_le_div_iff₀ hden hhalf).mpr (by simpa using hp)
  simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hr (by norm_num : (0 : ℝ) ≤ 2)

end Lax342547Proofs.HistogramGram
