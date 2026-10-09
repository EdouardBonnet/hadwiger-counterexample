import Lax342547Proofs.FiniteUniform

namespace Lax342547Proofs.FiniteProbability

open scoped ENNReal

theorem event_add_compl {α : Type} [Fintype α] (p : PMF α) (S : Set α) :
    p.toOuterMeasure S + p.toOuterMeasure Sᶜ = 1 := by
  classical
  rw [PMF.toOuterMeasure_apply_fintype, PMF.toOuterMeasure_apply_fintype,
    ← Finset.sum_add_distrib]
  calc
    _ = ∑ x, p x := Finset.sum_congr rfl (fun x _ => by by_cases h : x ∈ S <;> simp [h])
    _ = 1 := by simpa only [tsum_fintype] using p.tsum_coe

theorem event_ge_of_compl_le {α : Type} [Fintype α] (p : PMF α) (S : Set α)
    (ε : ℝ≥0∞) (h : p.toOuterMeasure Sᶜ ≤ ε) : 1 - ε ≤ p.toOuterMeasure S := by
  apply tsub_le_iff_right.mpr
  rw [← event_add_compl p S]
  exact add_le_add le_rfl h

theorem uniform_product_event {α β : Type} [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
    (S : Set (α × β)) :
    (PMF.uniformOfFintype (α × β)).toOuterMeasure S =
      ∑ a, PMF.uniformOfFintype α a *
        (PMF.uniformOfFintype β).toOuterMeasure {b | (a, b) ∈ S} := by
  classical
  rw [PMF.toOuterMeasure_apply_fintype, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [PMF.toOuterMeasure_apply_fintype, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  by_cases h : (a, b) ∈ S <;> simp [h, PMF.uniformOfFintype_apply, ENNReal.mul_inv]

theorem uniform_subtype_event {α : Type} [Fintype α] [Nonempty α]
    (S T : Set α) [Fintype S] [Nonempty S] :
    (PMF.uniformOfFintype α).toOuterMeasure (S ∩ T) =
      (PMF.uniformOfFintype α).toOuterMeasure S *
        (PMF.uniformOfFintype S).toOuterMeasure {x : S | x.val ∈ T} := by
  classical
  let e : ↥(S ∩ T) ≃ {x : S // x.val ∈ T} :=
    { toFun := fun x => ⟨⟨x.val, x.property.1⟩, x.property.2⟩
      invFun := fun x => ⟨x.val.val, x.val.property, x.property⟩
      left_inv := fun x => rfl
      right_inv := fun x => rfl }
  rw [PMF.toOuterMeasure_uniformOfFintype_apply, PMF.toOuterMeasure_uniformOfFintype_apply,
    PMF.toOuterMeasure_uniformOfFintype_apply, Fintype.card_congr e]
  have hS : (Fintype.card S : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero (α := S))
  simp only [div_eq_mul_inv]
  calc
    _ = (1 : ℝ≥0∞) *
        ((Fintype.card {x : S // x.val ∈ T} : ℝ≥0∞) * (Fintype.card α : ℝ≥0∞)⁻¹) := by simp
    _ = ((Fintype.card S : ℝ≥0∞) * (Fintype.card S : ℝ≥0∞)⁻¹) *
        ((Fintype.card {x : S // x.val ∈ T} : ℝ≥0∞) * (Fintype.card α : ℝ≥0∞)⁻¹) := by
      rw [ENNReal.mul_inv_cancel hS (by simp)]
    _ = _ := by ac_rfl

end Lax342547Proofs.FiniteProbability
