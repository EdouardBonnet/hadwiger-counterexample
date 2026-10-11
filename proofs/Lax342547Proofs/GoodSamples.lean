import Lax342547.GoodSamples
import Lax342547.CellAveraging
import Lax342547.DisjointSampling
import Lax342547.FiniteSampling

namespace Lax342547Proofs.GoodSamples
open Lax342547.GoodSamples

set_option backward.isDefEq.respectTransparency false
open Lax342547.RelativeEntropy Lax342547.FiniteSampling Lax342547.RetainedImages Lax342547.CellAveraging
open scoped BigOperators

/--
---
conclusion: Lax342547.GoodSamples.cell_mass_or
---
-/
theorem cell_mass_or {Ω : Type} [Fintype Ω]
    (ρ : Ω → ℝ) (S T : Ω → Prop) (hρ : ∀ x, 0 ≤ ρ x) :
    cellMass ρ (fun x => S x ∨ T x) ≤ cellMass ρ S+cellMass ρ T := by
  classical
  unfold cellMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x _
  by_cases hs : S x <;> by_cases ht : T x <;> simp [hs,ht,hρ x]

/--
---
conclusion: Lax342547.GoodSamples.bad_sample_bound
---
-/
theorem bad_sample_bound {Ω : Type} [Fintype Ω] (μ : Ω → ℝ) (S : Ω → Prop) (E : Ω → Ω → Prop)
    (m k : ℕ) (M κ : ℝ) (hμ : Probability μ) (_hM : 0 < M) (_hκ : 0 < κ)
    (hS : cellMass μ S < 1/M) (hE : pairEventMass μ μ E < 1/κ) :
    cellMass (productLaw (fun _ : Fin m => μ)) (Bad S E k) ≤
      (m.choose k : ℝ)*(1/M)^k+(m : ℝ)^(2*k)*(1/κ)^k := by
  classical
  have hp := Lax342547.FiniteSampling.product_probability (fun _ : Fin m => μ) (fun _ => hμ)
  have h₁ := Lax342547.FiniteSampling.exceptional_positions_bound (ι := Fin m) μ S k hμ
  have h₂ := Lax342547.DisjointSampling.disjoint_pair_exception_bound (ι := Fin m) μ E k hμ
  simp only [Fintype.card_fin] at h₁ h₂
  have hSn : 0 ≤ cellMass μ S := by
    unfold cellMass
    exact Finset.sum_nonneg (fun x _ => by split_ifs; exact hμ.1 x; exact le_rfl)
  have hEn := Lax342547.CellAveraging.pair_event_mass_nonneg μ μ E hμ.1 hμ.1
  have hS' := pow_le_pow_left₀ hSn hS.le k
  have hE' := pow_le_pow_left₀ hEn hE.le k
  have hu := Lax342547.GoodSamples.cell_mass_or (productLaw (fun _ : Fin m => μ))
    (fun sample => k ≤ (Finset.univ.filter (fun i => S (sample i))).card)
    (fun sample => ∃ a : Fin k × Bool ↪ Fin m, ∀ j, E (sample (a (j,false))) (sample (a (j,true)))) hp.1
  exact hu.trans (add_le_add
    (h₁.trans (mul_le_mul_of_nonneg_left hS' (Nat.cast_nonneg _)))
    (h₂.trans (mul_le_mul_of_nonneg_left hE' (pow_nonneg (Nat.cast_nonneg _) _))))

/--
---
conclusion: Lax342547.GoodSamples.mass_less_one_exists_complement
---
-/
theorem mass_less_one_exists_complement {Ω : Type} [Fintype Ω]
    (ρ : Ω → ℝ) (A : Ω → Prop) (hρ : Probability ρ) (hA : cellMass ρ A < 1) : ∃ x, ¬ A x := by
  classical
  by_contra hn
  push Not at hn
  have hh : cellMass ρ A = 1 := by simp [cellMass,hn,hρ.2]
  rw [hh] at hA
  exact lt_irrefl 1 hA

/--
---
conclusion: Lax342547.GoodSamples.exists_good_sample
---
-/
theorem exists_good_sample {Ω J : Type} [Fintype Ω]
    (μ : Ω → ℝ) (C : Finset J) (S : J → Ω → Prop) (E : J → Ω → Ω → Prop)
    (m k : ℕ) (M κ : ℝ) (hμ : Probability μ) (hM : 0 < M) (hκ : 0 < κ)
    (hS : ∀ c ∈ C, cellMass μ (S c) < 1/M)
    (hE : ∀ c ∈ C, pairEventMass μ μ (E c) < 1/κ)
    (hbudget : (C.card : ℝ)*((m.choose k : ℝ)*(1/M)^k+(m : ℝ)^(2*k)*(1/κ)^k) < 1) :
    ∃ sample : Fin m → Ω, ∀ c ∈ C, ¬ Bad (S c) (E c) k sample := by
  classical
  have hp := Lax342547.FiniteSampling.product_probability (fun _ : Fin m => μ) (fun _ => hμ)
  have hh := Lax342547.FiniteSampling.cell_mass_union_bound
    (productLaw (fun _ : Fin m => μ)) (fun c => Bad (S c) (E c) k) C hp.1
  have hloc : (∑ c ∈ C, cellMass (productLaw (fun _ : Fin m => μ)) (Bad (S c) (E c) k)) ≤
      (C.card : ℝ)*((m.choose k : ℝ)*(1/M)^k+(m : ℝ)^(2*k)*(1/κ)^k) := by
    calc
      _ ≤ ∑ c ∈ C, ((m.choose k : ℝ)*(1/M)^k+(m : ℝ)^(2*k)*(1/κ)^k) :=
        Finset.sum_le_sum (fun c hc => Lax342547.GoodSamples.bad_sample_bound μ (S c) (E c) m k M κ hμ hM hκ (hS c hc) (hE c hc))
      _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]
  obtain ⟨sample,hgood⟩ := Lax342547.GoodSamples.mass_less_one_exists_complement _ _ hp (hh.trans hloc |>.trans_lt hbudget)
  refine ⟨sample,?_⟩
  intro c hc hb
  exact hgood ⟨c,hc,hb⟩

end Lax342547Proofs.GoodSamples
