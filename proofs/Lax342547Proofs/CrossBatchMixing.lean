import Lax342547.CrossBatchMixing
import Lax342547Proofs.ConditionedMixing
import Lax342547Proofs.SlotWalsh

namespace Lax342547Proofs.CrossBatchMixing

open Lax342547.MomentSpace Lax342547.SlotWalsh Lax342547.CrossBatchMixing
open Lax342547.Walsh Lax342547.FourierTests Lax342547.RelativeEntropy
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

theorem bitMatrix_sum {I J S : Type} [Fintype S] (C : S → Matrix I J Binary)
    (t : S → Binary) (N : ℕ) : bitMatrix (coefficient C t) N = ∑ s,t s • bitMatrix (C s) N := by
  classical
  ext ⟨a,i⟩ ⟨b,j⟩
  by_cases h : a = b <;> simp [bitMatrix,coefficient,h,Matrix.sum_apply,Matrix.smul_apply]

theorem coefficient_phase {I J S : Type} [Fintype I] [Fintype J] [Fintype S]
    (C : S → Matrix I J Binary) (N : ℕ) (t : S → Binary)
    (xy : ((Fin N × I → Binary) × (Fin N × J → Binary))) :
    phase t (crossBits C N xy) = phase xy.1 ((bitMatrix (coefficient C t) N).mulVec xy.2) := by
  classical
  unfold phase
  congr 1
  rw [bitMatrix_sum,Matrix.sum_mulVec,dotProduct_sum]
  unfold crossBits dotProduct
  apply Finset.sum_congr rfl
  intro s _
  simp only [Matrix.smul_mulVec,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

/--
---
conclusion: Lax342547.CrossBatchMixing.weighted_character_bound
---
-/
theorem weighted_character_bound {I J S : Type} [Fintype I] [Fintype J] [Fintype S]
    [DecidableEq I] [DecidableEq J] (C : S → Matrix I J Binary) (N : ℕ)
    (α f : (Fin N × I → Binary) → ℝ) (β g : (Fin N × J → Binary) → ℝ)
    (target t : S → Binary) (C₁ C₂ : ℝ)
    (hα : ∀ x,0 ≤ α x ∧ α x ≤ C₁/(2 : ℝ)^(N*Fintype.card I))
    (hβ : ∀ y,0 ≤ β y ∧ β y ≤ C₂/(2 : ℝ)^(N*Fintype.card J))
    (hf : ∀ x,|f x| ≤ 1) (hg : ∀ y,|g y| ≤ 1)
    (hC : coefficient C t ≠ 0) :
    |characterMean (fun xy : (Fin N × I → Binary) × (Fin N × J → Binary) =>
      α xy.1*β xy.2*(f xy.1*g xy.2)) (crossBits C N) target t| ≤
      C₁*C₂/Real.sqrt ((2 : ℝ)^N) := by
  classical
  let p := (2 : ℝ)^(N*Fintype.card I)
  let q := (2 : ℝ)^(N*Fintype.card J)
  have hp : 0 < p := by positivity
  have hq : 0 < q := by positivity
  have hc₁ : ∀ x,0 ≤ p*α x ∧ p*α x ≤ C₁ := fun x =>
    ⟨mul_nonneg hp.le (hα x).1,by have hh := (le_div_iff₀ hp).mp (hα x).2; simpa only [mul_comm] using hh⟩
  have hc₂ : ∀ y,0 ≤ q*β y ∧ q*β y ≤ C₂ := fun y =>
    ⟨mul_nonneg hq.le (hβ y).1,by have hh := (le_div_iff₀ hq).mp (hβ y).2; simpa only [mul_comm] using hh⟩
  have hh := Lax342547Proofs.BilinearWalsh.density_bound (bitMatrix (coefficient C t) N)
    (fun x => p*α x) f (fun y => q*β y) g C₁ C₂ hc₁ hc₂ hf hg
  rw [Lax342547Proofs.SlotWalsh.bit_rank] at hh
  have hr : N ≤ N*(coefficient C t).rank := Nat.le_mul_of_pos_right N
    (Lax342547Proofs.SlotWalsh.rank_pos_of_ne_zero _ hC)
  have he : Lax342547.BilinearWalsh.average (bitMatrix (coefficient C t) N)
      (fun x => (p*α x)*f x) (fun y => (q*β y)*g y) =
      ∑ xy : (Fin N × I → Binary) × (Fin N × J → Binary),
        α xy.1*β xy.2*(f xy.1*g xy.2)*phase xy.1 ((bitMatrix (coefficient C t) N).mulVec xy.2) := by
    unfold Lax342547.BilinearWalsh.average Lax342547.BilinearWalsh.correlation
    simp only [Fintype.card_prod,Fintype.card_fin]
    rw [Fintype.sum_prod_type]
    have hs : (∑ x,∑ y,((p*α x)*f x)*((q*β y)*g y)*
        phase x ((bitMatrix (coefficient C t) N).mulVec y)) =
        (p*q)*(∑ x,∑ y,α x*β y*(f x*g y)*phase x ((bitMatrix (coefficient C t) N).mulVec y)) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      ring
    rw [hs]
    exact mul_div_cancel_left₀ _ (ne_of_gt (mul_pos hp hq))
  rw [he] at hh
  have hsign : |phase t target| = 1 := by
    unfold phase
    rcases Lax342547Proofs.Walsh.binary_cases (dotProduct t target) with hz | hz <;> rw [hz] <;> simp
  have hmean : characterMean (fun xy : (Fin N × I → Binary) × (Fin N × J → Binary) =>
      α xy.1*β xy.2*(f xy.1*g xy.2)) (crossBits C N) target t =
      (∑ xy : (Fin N × I → Binary) × (Fin N × J → Binary),
        α xy.1*β xy.2*(f xy.1*g xy.2)*phase xy.1 ((bitMatrix (coefficient C t) N).mulVec xy.2))*phase t target := by
    simp only [characterMean,coefficient_phase,Finset.sum_mul]
  rw [hmean,abs_mul,hsign,mul_one]
  refine hh.trans ?_
  have hc : 0 ≤ C₁*C₂ := by
    have h₁ := hc₁ 0
    have h₂ := hc₂ 0
    exact mul_nonneg (h₁.1.trans h₁.2) (h₂.1.trans h₂.2)
  gcongr
  norm_num

theorem bounded_mean {X : Type} [Fintype X] (ρ f : X → ℝ)
    (hρ : Probability ρ) (hf : ∀ x,|f x| ≤ 1) : |∑ x,ρ x*f x| ≤ 1 := by
  have hs : (∑ x,|ρ x*f x|) ≤ ∑ x,ρ x := by
    apply Finset.sum_le_sum
    intro x _
    rw [abs_mul,abs_of_nonneg (hρ.1 x)]
    exact (mul_le_mul_of_nonneg_left (hf x) (hρ.1 x)).trans_eq (mul_one _)
  exact (Finset.abs_sum_le_sum_abs (s := Finset.univ) (f := fun x => ρ x*f x)).trans (hs.trans_eq hρ.2)

/--
---
conclusion: Lax342547.CrossBatchMixing.cross_batch_comparison
---
-/
theorem cross_batch_comparison {I J S : Type} [Fintype I] [Fintype J] [Fintype S]
    [DecidableEq I] [DecidableEq J] [DecidableEq S] (C : S → Matrix I J Binary) (N : ℕ)
    (α f : (Fin N × I → Binary) → ℝ) (β g : (Fin N × J → Binary) → ℝ)
    (target : S → Binary) (C₁ C₂ : ℝ)
    (hα : Probability α) (hβ : Probability β)
    (hcapA : ∀ x,α x ≤ C₁/(2 : ℝ)^(N*Fintype.card I))
    (hcapB : ∀ y,β y ≤ C₂/(2 : ℝ)^(N*Fintype.card J))
    (hf : ∀ x,|f x| ≤ 1) (hg : ∀ y,|g y| ≤ 1)
    (hC : ∀ t : S → Binary,t ≠ 0 → coefficient C t ≠ 0)
    (hsmall : C₁*C₂/Real.sqrt ((2 : ℝ)^N) ≤ 1/(2 : ℝ)^(Fintype.card S+1)) :
    |patternMass (fun xy : (Fin N × I → Binary) × (Fin N × J → Binary) =>
        α xy.1*β xy.2*(f xy.1*g xy.2)) (crossBits C N) target/
        patternMass (fun xy : (Fin N × I → Binary) × (Fin N × J → Binary) =>
          α xy.1*β xy.2) (crossBits C N) target-
        (∑ x,α x*f x)*(∑ y,β y*g y)| ≤
      (2 : ℝ)^(Fintype.card S+2)*(C₁*C₂/Real.sqrt ((2 : ℝ)^N)) := by
  classical
  let ε := C₁*C₂/Real.sqrt ((2 : ℝ)^N)
  let ρ := fun xy : (Fin N × I → Binary) × (Fin N × J → Binary) => α xy.1*β xy.2
  have heps : 0 ≤ ε := by
    have ha : 0 ≤ C₁ := by
      have hh := (hα.1 0).trans (hcapA 0)
      have hr := (le_div_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ)^(N*Fintype.card I))).mp hh
      simpa only [zero_mul] using hr
    have hb : 0 ≤ C₂ := by
      have hh := (hβ.1 0).trans (hcapB 0)
      have hr := (le_div_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ)^(N*Fintype.card J))).mp hh
      simpa only [zero_mul] using hr
    exact div_nonneg (mul_nonneg ha hb) (Real.sqrt_nonneg _)
  have htotal : ∑ xy,ρ xy = 1 := by
    simp only [ρ,Fintype.sum_prod_type,← Finset.mul_sum,hβ.2,mul_one,hα.2]
  have hc (t : S → Binary) (ht : t ≠ 0) := weighted_character_bound C N α f β g target t C₁ C₂
    (fun x => ⟨hα.1 x,hcapA x⟩) (fun y => ⟨hβ.1 y,hcapB y⟩) hf hg (hC t ht)
  have hc0 (t : S → Binary) (ht : t ≠ 0) : |characterMean ρ (crossBits C N) target t| ≤ ε := by
    simpa only [mul_one,ρ] using weighted_character_bound C N α (fun _ => 1) β (fun _ => 1) target t C₁ C₂
      (fun x => ⟨hα.1 x,hcapA x⟩) (fun y => ⟨hβ.1 y,hcapB y⟩) (by norm_num) (by norm_num) (hC t ht)
  have hq : 1/(2 : ℝ)^(Fintype.card S+1) ≤ patternMass ρ (crossBits C N) target :=
    Lax342547Proofs.FourierTests.scalar_agreement_half ρ (crossBits C N) target ε heps htotal
      (fun t ht => (abs_le.mp (hc0 t ht)).1) hsmall
  have hqpos : 0 < patternMass ρ (crossBits C N) target := lt_of_lt_of_le (by positivity) hq
  have he : (∑ xy,ρ xy*(f xy.1*g xy.2)) = (∑ x,α x*f x)*(∑ y,β y*g y) := by
    simp only [ρ,Fintype.sum_prod_type]
    rw [Finset.sum_mul]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    ring
  have hm : |∑ xy,ρ xy*(f xy.1*g xy.2)| ≤ 1 := by
    rw [he,abs_mul]
    exact (mul_le_mul (bounded_mean α f hα hf) (bounded_mean β g hβ hg) (abs_nonneg _) (by norm_num)).trans_eq (one_mul 1)
  have hh := Lax342547Proofs.ConditionedMixing.conditional_test_comparison ρ
    (fun xy => f xy.1*g xy.2) (crossBits C N) target ε heps htotal hm hc0 hc hqpos
  rw [he] at hh
  refine hh.trans ?_
  have hdiv := div_le_div_of_nonneg_left (by positivity : 0 ≤ 2*ε) (by positivity : (0 : ℝ) < 1/(2 : ℝ)^(Fintype.card S+1)) hq
  have hpow : (2*ε)/(1/(2 : ℝ)^(Fintype.card S+1)) = (2 : ℝ)^(Fintype.card S+2)*ε := by
    rw [pow_succ]
    field_simp
    ring
  exact hdiv.trans_eq hpow

end Lax342547Proofs.CrossBatchMixing
