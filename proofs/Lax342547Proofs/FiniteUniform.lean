import Lax342547Proofs.FiniteLinearLaw

namespace Lax342547Proofs.FiniteUniform

open scoped ENNReal

theorem map_eq_of_fibers {α β : Type} [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
    (f : α → β) (hf : ∀ y z, Nonempty ({x : α // f x = y} ≃ {x : α // f x = z})) :
    (PMF.uniformOfFintype α).map f = PMF.uniformOfFintype β := by
  classical
  ext y
  have hc (z : β) : Fintype.card {x : α // f x = z} = Fintype.card {x : α // f x = y} :=
    Fintype.card_congr (hf z y).some
  have hcard : Fintype.card α =
      Fintype.card {x : α // f x = y} * Fintype.card β := by
    rw [← Fintype.card_congr (Equiv.sigmaFiberEquiv f), Fintype.card_sigma]
    simp [hc, Nat.mul_comm]
  have hne : (Fintype.card {x : α // f x = y} : ℝ≥0∞) ≠ 0 := by
    have h : Fintype.card {x : α // f x = y} ≠ 0 := by
      intro h
      rw [h, zero_mul] at hcard
      exact Fintype.card_ne_zero hcard
    exact_mod_cast h
  rw [FiniteLinearLaw.map_uniform_apply, Nat.card_eq_fintype_card,
    PMF.uniformOfFintype_apply, hcard, Nat.cast_mul]
  simpa only [mul_one, one_div] using
    ENNReal.mul_div_mul_left 1 (Fintype.card β) hne (by simp)

theorem map_eq_of_transport {α β : Type} [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
    (f : α → β)
    (hf : ∀ y z, ∃ e : α ≃ α, ∀ x, f (e x) = z ↔ f x = y) :
    (PMF.uniformOfFintype α).map f = PMF.uniformOfFintype β := by
  apply map_eq_of_fibers
  intro y z
  obtain ⟨e, he⟩ := hf y z
  exact ⟨{
    toFun := fun x => ⟨e x.val, (he x.val).mpr x.property⟩
    invFun := fun x => ⟨e.symm x.val, (he (e.symm x.val)).mp (by simpa using x.property)⟩
    left_inv := fun x => by ext; simp
    right_inv := fun x => by ext; simp }⟩

theorem map_equiv {α β : Type} [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
    (e : α ≃ β) : (PMF.uniformOfFintype α).map e = PMF.uniformOfFintype β := by
  classical
  ext y
  rw [PMF.map_apply]
  have h : (fun x : α => if y = e x then PMF.uniformOfFintype α x else 0) =
      fun x => if x = e.symm y then (Fintype.card α : ℝ≥0∞)⁻¹ else 0 := by
    funext x
    have he : y = e x ↔ x = e.symm y := by
      constructor
      · intro he
        rw [he, e.symm_apply_apply]
      · intro he
        rw [he, e.apply_symm_apply]
    simp only [PMF.uniformOfFintype_apply, he]
  rw [h]
  simp [Fintype.card_congr e]

theorem map_subtype_apply {α : Type} [Fintype α] (S : Set α) [Fintype S] [Nonempty S]
    [DecidablePred (· ∈ S)]
    (x : α) : (PMF.uniformOfFintype S).map Subtype.val x =
      if x ∈ S then (Fintype.card S : ℝ≥0∞)⁻¹ else 0 := by
  classical
  rw [PMF.map_apply]
  by_cases hx : x ∈ S
  · rw [if_pos hx]
    have h : (fun a : S => if x = a.val then PMF.uniformOfFintype S a else 0) =
        fun a => if a = ⟨x, hx⟩ then (Fintype.card S : ℝ≥0∞)⁻¹ else 0 := by
      funext a
      simp [Subtype.ext_iff, eq_comm]
    rw [h]
    simp
  · rw [if_neg hx]
    apply ENNReal.tsum_eq_zero.mpr
    intro a
    simp [show x ≠ a.val from fun he => hx (he ▸ a.property)]

theorem filter_uniform {α : Type} [Fintype α] [Nonempty α]
    (S : Set α) [Fintype S] [Nonempty S]
    (h : ∃ a ∈ S, a ∈ (PMF.uniformOfFintype α).support) :
    (PMF.uniformOfFintype α).filter S h = (PMF.uniformOfFintype S).map Subtype.val := by
  classical
  ext x
  rw [PMF.filter_apply, ← PMF.toOuterMeasure_apply,
    PMF.toOuterMeasure_uniformOfFintype_apply, map_subtype_apply]
  by_cases hx : x ∈ S
  · rw [Set.indicator_of_mem hx, if_pos hx, PMF.uniformOfFintype_apply,
      ENNReal.inv_div (Or.inl (by simp)) (Or.inl (by simp))]
    rw [div_eq_mul_inv, ← mul_assoc, ENNReal.inv_mul_cancel (by simp) (by simp), one_mul]
  · simp [hx]

end Lax342547Proofs.FiniteUniform
