import Lax342547.AdaptiveUnion
import Lax342547Proofs.AdaptiveSets

namespace Lax342547Proofs.AdaptiveUnion
open Lax342547.AdaptiveUnion

set_option backward.isDefEq.respectTransparency false
open Lax342547.RelativeEntropy Lax342547.FiniteSampling Lax342547.RetainedImages
open scoped BigOperators

/--
---
conclusion: Lax342547.AdaptiveUnion.adaptive_cover_union
---
-/
theorem adaptive_cover_union {ι Ω : Type} [Fintype ι] [Fintype Ω] [DecidableEq ι]
    (μ : Ω → ℝ) (A : ∀ E : Finset ι, (E → Ω) → Ω → Prop) (p : ℝ) (k : ℕ)
    (hμ : Probability μ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hA : ∀ E exposed, cellMass μ (A E exposed) ≤ p) :
    cellMass (productLaw (fun _ : ι => μ))
      (fun sample => ∃ E J : Finset ι, Disjoint E J ∧ k ≤ J.card ∧
        ∀ j ∈ J, A E (fun e => sample e.val) (sample j)) ≤
      (4 : ℝ)^Fintype.card ι*p^k := by
  classical
  let Q := (Finset.univ.powerset ×ˢ Finset.univ.powerset).filter
    (fun t : Finset ι × Finset ι => Disjoint t.1 t.2 ∧ k ≤ t.2.card)
  let B := fun t : Finset ι × Finset ι => fun sample : ι → Ω =>
    ∀ j ∈ t.2, A t.1 (fun e => sample e.val) (sample j)
  have hprob := Lax342547Proofs.FiniteSampling.product_probability (fun _ : ι => μ) (fun _ => hμ)
  have hmono : ∀ sample : ι → Ω,
      (∃ E J : Finset ι, Disjoint E J ∧ k ≤ J.card ∧ ∀ j ∈ J, A E (fun e => sample e.val) (sample j)) →
      ∃ t ∈ Q, B t sample := by
    rintro sample ⟨E,J,hd,hk,hh⟩
    refine ⟨(E,J),?_,hh⟩
    simp [Q,hd,hk]
  have htail : ∀ t ∈ Q, cellMass (productLaw (fun _ : ι => μ)) (B t) ≤ p^k := by
    intro t ht
    have ht' := (Finset.mem_filter.mp ht).2
    exact (Lax342547Proofs.AdaptiveSets.disjoint_adaptive_bound μ t.1 t.2 ht'.1
      (A t.1) p hμ (hA t.1)).trans (pow_le_pow_of_le_one hp0 hp1 ht'.2)
  have hcount : Q.card ≤ 4^Fintype.card ι := by
    calc
      _ ≤ (Finset.univ.powerset ×ˢ Finset.univ.powerset : Finset (Finset ι × Finset ι)).card := Finset.card_filter_le _ _
      _ = _ := by rw [Finset.card_product,Finset.card_powerset,Finset.card_univ,← mul_pow]; norm_num
  calc
    _ ≤ cellMass (productLaw (fun _ : ι => μ)) (fun sample => ∃ t ∈ Q, B t sample) :=
      Lax342547Proofs.FiniteSampling.cell_mass_mono _ _ _ hprob.1 hmono
    _ ≤ ∑ t ∈ Q, cellMass (productLaw (fun _ : ι => μ)) (B t) :=
      Lax342547Proofs.FiniteSampling.cell_mass_union_bound _ _ Q hprob.1
    _ ≤ ∑ t ∈ Q, p^k := Finset.sum_le_sum htail
    _ = (Q.card : ℝ)*p^k := by simp [nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcount) (pow_nonneg hp0 _)

end Lax342547Proofs.AdaptiveUnion
