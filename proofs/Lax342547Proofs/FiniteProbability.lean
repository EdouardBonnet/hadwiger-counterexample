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

theorem uniform_subtype_bound_factor {α : Type} [Fintype α] [Nonempty α]
    (S T : Set α) [Fintype S] [Nonempty S] (c : ℝ≥0∞)
    (hc : 1 ≤ c * (PMF.uniformOfFintype α).toOuterMeasure S) :
    (PMF.uniformOfFintype S).toOuterMeasure {x : S | x.val ∈ T} ≤
      c * (PMF.uniformOfFintype α).toOuterMeasure T := by
  let q := (PMF.uniformOfFintype S).toOuterMeasure {x : S | x.val ∈ T}
  calc
    q = 1 * q := (one_mul q).symm
    _ ≤ (c * (PMF.uniformOfFintype α).toOuterMeasure S) * q :=
      mul_le_mul_of_nonneg_right hc zero_le
    _ = c * (PMF.uniformOfFintype α).toOuterMeasure (S ∩ T) := by
      rw [mul_assoc, uniform_subtype_event S T]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      ((PMF.uniformOfFintype α).toOuterMeasure.mono Set.inter_subset_right) zero_le

theorem point_density_of_constant {α : Type} [Fintype α] [Nonempty α]
    (p : PMF α) (y : α) (S : Set α) (c : ℝ≥0∞)
    (hS : ∀ x ∈ S, p x = p y)
    (hc : 1 ≤ c * (PMF.uniformOfFintype α).toOuterMeasure S) :
    p y ≤ c * PMF.uniformOfFintype α y := by
  classical
  let u := PMF.uniformOfFintype α
  have he : p y * u.toOuterMeasure S = u y * p.toOuterMeasure S := by
    rw [PMF.toOuterMeasure_apply_fintype, PMF.toOuterMeasure_apply_fintype,
      Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : x ∈ S
    · simp [hx, hS x hx, u, PMF.uniformOfFintype_apply, mul_comm]
    · simp [hx]
  have hp : p.toOuterMeasure S ≤ 1 := by
    calc
      _ ≤ p.toOuterMeasure Set.univ := p.toOuterMeasure.mono (Set.subset_univ S)
      _ = 1 := by simpa [PMF.toOuterMeasure_apply] using p.tsum_coe
  calc
    p y = p y * 1 := (mul_one _).symm
    _ ≤ p y * (c * u.toOuterMeasure S) := mul_le_mul_of_nonneg_left hc zero_le
    _ = c * (p y * u.toOuterMeasure S) := by ac_rfl
    _ = (c * u y) * p.toOuterMeasure S := by rw [he, mul_assoc]
    _ ≤ (c * u y) * 1 := mul_le_mul_of_nonneg_left hp zero_le
    _ = _ := mul_one _

end Lax342547Proofs.FiniteProbability
