import Lax342547.FiniteLinearLaw
import Mathlib.LinearAlgebra.Dimension.Constructions
import Lean.Elab.Tactic.Omega

namespace Lax342547Proofs.FiniteLinearLaw

set_option backward.isDefEq.respectTransparency false

/--
---
conclusion: Lax342547.FiniteLinearLaw.codimension_map_le
---
A surjective map induces a surjection between the quotients by S and
its image. Compare quotient dimensions and apply rank-nullity.
-/
theorem codimension_map_le {K V W : Type} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K V] [FiniteDimensional K W]
    (f : V →ₗ[K] W) (hf : Function.Surjective f) (S : Submodule K V) :
    Module.finrank K W - Module.finrank K (S.map f) ≤ Module.finrank K V - Module.finrank K S := by
  let q := S.mapQ (S.map f) f (Submodule.le_comap_map f S)
  have hq : Function.Surjective q := by
    apply LinearMap.range_eq_top.mp
    rw [Submodule.range_mapQ, LinearMap.range_eq_top.mpr hf, Submodule.map_top, Submodule.range_mkQ]
  have h := LinearMap.finrank_le_finrank_of_surjective hq
  have hS := S.finrank_quotient_add_finrank
  have hSf := (S.map f).finrank_quotient_add_finrank
  omega

open Lax342547.MomentSpace
open scoped ENNReal

variable {V W : Type} [AddCommGroup V] [Module Binary V] [AddCommGroup W] [Module Binary W]
  [Fintype V] [Fintype W] [FiniteDimensional Binary V] [FiniteDimensional Binary W]

theorem binary_card (U : Type) [AddCommGroup U] [Module Binary U] [Fintype U]
    [FiniteDimensional Binary U] : Fintype.card U = 2 ^ Module.finrank Binary U := by
  classical
  rw [Fintype.card_congr (Module.finBasis Binary U).equivFun.toEquiv]
  simp [Binary, ZMod.card]

omit [Fintype W] [FiniteDimensional Binary V] [FiniteDimensional Binary W] in
theorem fiber_card_le_kernel (f : V →ₗ[Binary] W) (y : W) :
    Nat.card {x : V // f x = y} ≤ Nat.card (LinearMap.ker f) := by
  classical
  by_cases hy : y ∈ LinearMap.range f
  · obtain ⟨x₀, hx₀⟩ := hy
    let g : {x : V // f x = y} → LinearMap.ker f :=
      fun x => ⟨x.val - x₀, by simp [LinearMap.mem_ker, x.property, hx₀]⟩
    have hg : Function.Injective g := by
      intro x z hxz
      apply Subtype.ext
      exact sub_left_injective (congrArg Subtype.val hxz)
    simpa only [Nat.card_eq_fintype_card] using Fintype.card_le_of_injective g hg
  · have : IsEmpty {x : V // f x = y} := ⟨fun x => hy ⟨x.val, x.property⟩⟩
    simp [Nat.card_eq_fintype_card]

theorem fiber_density_bound (f : V →ₗ[Binary] W) (c : ℕ)
    (hc : Module.finrank Binary W ≤ Module.finrank Binary (LinearMap.range f) + c) (y : W) :
    Nat.card {x : V // f x = y} * Fintype.card W ≤ 2 ^ c * Fintype.card V := by
  classical
  have hdim := f.finrank_range_add_finrank_ker
  calc
    _ ≤ Fintype.card (LinearMap.ker f) * Fintype.card W :=
      Nat.mul_le_mul_right _ (by simpa only [Nat.card_eq_fintype_card] using fiber_card_le_kernel f y)
    _ = 2 ^ (Module.finrank Binary (LinearMap.ker f) + Module.finrank Binary W) := by
      rw [binary_card (LinearMap.ker f), binary_card W, pow_add]
    _ ≤ 2 ^ (c + Module.finrank Binary V) := Nat.pow_le_pow_right (by decide) (by omega)
    _ = 2 ^ c * Fintype.card V := by rw [binary_card V, pow_add]

theorem map_uniform_apply {α β : Type} [Fintype α] [Nonempty α] (f : α → β) (y : β) :
    (PMF.uniformOfFintype α).map f y = (Nat.card {x : α // f x = y} : ℝ≥0∞) / Fintype.card α := by
  classical
  rw [PMF.map_apply, tsum_fintype]
  simp_rw [PMF.uniformOfFintype_apply]
  rw [← Finset.sum_filter]
  simp [Nat.card_eq_fintype_card, Fintype.card_subtype, eq_comm, div_eq_mul_inv]

/--
---
conclusion: Lax342547.FiniteLinearLaw.uniform_image_bound
---
Every nonempty fiber is a translate of the kernel. Binary vector spaces
have 2^dimension elements, so rank-nullity bounds the fiber density by
2^c. Divide the cardinal inequality by the positive uniform denominators.
-/
theorem uniform_image_bound (f : V →ₗ[Binary] W) (c : ℕ)
    (hc : Module.finrank Binary W ≤ Module.finrank Binary (LinearMap.range f) + c) (y : W) :
    (PMF.uniformOfFintype V).map f y ≤ 2 ^ c * PMF.uniformOfFintype W y := by
  have h := fiber_density_bound f c hc y
  have h' : (Nat.card {x : V // f x = y} : ℝ≥0∞) * Fintype.card W ≤
      (2 : ℝ≥0∞) ^ c * Fintype.card V := by exact_mod_cast h
  have hV : (Fintype.card V : ℝ≥0∞) ≠ 0 := by simp
  have hW : (Fintype.card W : ℝ≥0∞) ≠ 0 := by simp
  rw [map_uniform_apply, PMF.uniformOfFintype_apply, ← div_eq_mul_inv]
  apply (ENNReal.div_le_iff hV (by simp)).mpr
  calc
    _ ≤ ((2 : ℝ≥0∞) ^ c * Fintype.card V) / Fintype.card W :=
      (ENNReal.le_div_iff_mul_le (Or.inl hW) (Or.inl (by simp))).mpr h'
    _ = _ := by simp only [div_eq_mul_inv]; exact mul_right_comm _ _ _

/--
---
conclusion: Lax342547.FiniteLinearLaw.uniform_image_of_surjective
---
All fibers of a surjective linear map are translates of its kernel.
Rank-nullity therefore gives equal normalized mass at every output.
-/
theorem uniform_image_of_surjective (f : V →ₗ[Binary] W) (hf : Function.Surjective f) :
    (PMF.uniformOfFintype V).map f = PMF.uniformOfFintype W := by
  classical
  have hcard : Fintype.card V = Fintype.card (LinearMap.ker f) * Fintype.card W := by
    have hd := f.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hf, finrank_top] at hd
    rw [binary_card V, binary_card (LinearMap.ker f), binary_card W, ← pow_add]
    congr 1
    omega
  ext y
  obtain ⟨x₀, hx₀⟩ := hf y
  let e : {x : V // f x = y} ≃ LinearMap.ker f :=
    { toFun := fun x => ⟨x.val - x₀, by simp [LinearMap.mem_ker, x.property, hx₀]⟩
      invFun := fun z => ⟨z.val + x₀, by simp [hx₀, show f z.val = 0 from z.property]⟩
      left_inv := fun x => by ext; simp
      right_inv := fun z => by ext; simp }
  have he := Fintype.card_congr e
  rw [map_uniform_apply, Nat.card_eq_fintype_card, he, PMF.uniformOfFintype_apply,
    hcard, Nat.cast_mul]
  simpa only [mul_one, one_div] using
    ENNReal.mul_div_mul_left 1 (Fintype.card W)
      (by exact_mod_cast (Fintype.card_ne_zero (α := LinearMap.ker f)))
      (by simp)

noncomputable def familyRangeEquiv {K T : Type} [Field K] {V W : T → Type}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (f : ∀ i, V i →ₗ[K] W i) :
    LinearMap.range (Lax342547.FiniteLinearLaw.familyMap f) ≃ₗ[K] (∀ i, LinearMap.range (f i)) where
  toFun x i := ⟨x.val i, by
    obtain ⟨v, hv⟩ := x.property
    exact ⟨v i, congrFun hv i⟩⟩
  invFun y := ⟨fun i => (y i).val, by
    choose v hv using fun i => (y i).property
    exact ⟨v, funext hv⟩⟩
  left_inv x := by apply Subtype.ext; rfl
  right_inv y := by funext i; apply Subtype.ext; rfl
  map_add' x y := rfl
  map_smul' a x := rfl

/--
---
conclusion: Lax342547.FiniteLinearLaw.family_codimension
---
The image of a coordinatewise family of linear maps is linearly
equivalent to the product of their images. Dimensions therefore add,
and summing the individual codimension bounds proves the joint bound.
-/
theorem family_codimension {K T : Type} [Field K] [Fintype T] {V W : T → Type}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    [∀ i, FiniteDimensional K (V i)] [∀ i, FiniteDimensional K (W i)]
    (f : ∀ i, V i →ₗ[K] W i) (c : T → ℕ)
    (hc : ∀ i, Module.finrank K (W i) ≤ Module.finrank K (LinearMap.range (f i)) + c i) :
    Module.finrank K (∀ i, W i) ≤
      Module.finrank K (LinearMap.range (Lax342547.FiniteLinearLaw.familyMap f)) + ∑ i, c i := by
  rw [(familyRangeEquiv f).finrank_eq, Module.finrank_pi_fintype, Module.finrank_pi_fintype,
    ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun i _ => hc i)

end Lax342547Proofs.FiniteLinearLaw
