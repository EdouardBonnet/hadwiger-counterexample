import Lax342547.AffineImages
import Lax342547Proofs.MixerCompatibility
import Lax342547.FiniteLinearLaw

namespace Lax342547Proofs.AffineImages

open Lax342547.MomentSpace Lax342547.AffineImages
open scoped ENNReal

variable {J T V : Type} [Fintype J] [Fintype T]
  [AddCommGroup V] [Module Binary V]

theorem evaluation_range (S : J → Submodule Binary V) (S₀ : Submodule Binary V)
    (hS : ∀ j, S₀ ≤ S j) (C : Matrix J T Binary) (hC : Function.Injective C.mulVec)
    (y : T → S₀) : (fun t => (y t).val) ∈ LinearMap.range (evaluation S C) := by
  classical
  obtain ⟨U, hU⟩ := MixerCompatibility.exists_left_inverse C hC
  let x : ∀ j, S j := fun j => ⟨∑ t, U t j • (y t).val,
    Submodule.sum_mem _ (fun t _ => (S j).smul_mem _ (hS j (y t).property))⟩
  refine ⟨x, ?_⟩
  ext t
  change (∑ j, C j t • ∑ s, U s j • (y s).val) = (y t).val
  simp_rw [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  have he (s : T) : ∑ j, C j t * U s j = (1 : Matrix T T Binary) s t := by
    simpa only [Matrix.mul_apply, mul_comm] using congrFun (congrFun hU s) t
  simp_rw [← Finset.sum_smul, he]
  simp [Matrix.one_apply, eq_comm]

/--
---
conclusion: Lax342547.AffineImages.evaluation_rank
---
A left inverse of the nominal coefficient matrix lifts any T-tuple of
common-subspace vectors to the allowed column spaces. Thus the image
contains an injective copy of the full T-fold common subspace.
-/
theorem evaluation_rank [FiniteDimensional Binary V]
    (S : J → Submodule Binary V) (S₀ : Submodule Binary V)
    (hS : ∀ j, S₀ ≤ S j) (C : Matrix J T Binary) (hC : Function.Injective C.mulVec) :
    Fintype.card T * Module.finrank Binary S₀ ≤
      Module.finrank Binary (LinearMap.range (evaluation S C)) := by
  let f : (T → S₀) →ₗ[Binary] LinearMap.range (evaluation S C) :=
    { toFun := fun y => ⟨fun t => (y t).val, evaluation_range S S₀ hS C hC y⟩
      map_add' := fun x y => rfl
      map_smul' := fun c x => rfl }
  have hf : Function.Injective f := by
    intro x y h
    funext t
    exact Subtype.ext (congrFun (congrArg Subtype.val h) t)
  simpa [Module.finrank_pi_fintype] using LinearMap.finrank_le_finrank_of_injective hf

/--
---
conclusion: Lax342547.AffineImages.image_bound
---
Apply the exact affine linear-image bound to the independent product of
column translation spaces. The rank estimate is t dim(S), uniformly in
the size t of the nominal tuple and in all column offsets.
-/
theorem image_bound [DecidableEq J] [FiniteDimensional Binary V]
    (S : J → Submodule Binary V) [∀ j, Fintype (S j)]
    (S₀ : Submodule Binary V) (hS : ∀ j, S₀ ≤ S j)
    (C : Matrix J T Binary) (hC : Function.Injective C.mulVec) (a : J → V) (y : T → V) :
    law S C a y ≤ 1 / (2 : ℝ≥0∞) ^ (Fintype.card T * Module.finrank Binary S₀) := by
  exact Lax342547.FiniteLinearLaw.uniform_affine_image_bound (evaluation S C) _ y _
    (Lax342547.AffineImages.evaluation_rank S S₀ hS C hC)

omit [Fintype T] in
theorem coefficient_target_bound [DecidableEq J] [FiniteDimensional Binary V]
    (S : J → Submodule Binary V) [∀ j, Fintype (S j)]
    (S₀ : Submodule Binary V) (hS : ∀ j, S₀ ≤ S j) (a : J → V)
    (c : J → Binary) (hc : c ≠ 0) (y : V) :
    (PMF.uniformOfFintype (∀ j, S j)).toOuterMeasure
      {x | columnMap (fun j => a j + (x j).val) c = y} ≤
      1 / (2 : ℝ≥0∞) ^ Module.finrank Binary S₀ := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, c j ≠ 0 := by
    by_contra h
    push Not at h
    exact hc (funext h)
  let C : Matrix J Unit Binary := fun j _ => c j
  have hC : Function.Injective C.mulVec := by
    intro x y h
    have he : c j * x () = c j * y () := by
      simpa [C, Matrix.mulVec, dotProduct] using congrFun h j
    funext u
    cases u
    exact mul_left_cancel₀ hj he
  have h := Lax342547.AffineImages.image_bound S S₀ hS C hC a (fun _ : Unit => y)
  rw [← PMF.toOuterMeasure_apply_singleton] at h
  change ((PMF.uniformOfFintype (∀ j, S j)).map _).toOuterMeasure _ ≤ _ at h
  rw [PMF.toOuterMeasure_map_apply] at h
  have hset : (fun x : ∀ j, S j => (fun t : Unit => ∑ j, C j t • a j) + evaluation S C x) ⁻¹'
      {fun _ : Unit => y} = {x | columnMap (fun j => a j + (x j).val) c = y} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq, funext_iff]
    simp [C, evaluation, columnMap, smul_add, Finset.sum_add_distrib]
  rw [hset] at h
  simpa only [Fintype.card_unit, one_mul] using h

omit [Fintype T] in
theorem coefficient_bound [DecidableEq J] [FiniteDimensional Binary V]
    (S : J → Submodule Binary V) [∀ j, Fintype (S j)]
    (S₀ : Submodule Binary V) (hS : ∀ j, S₀ ≤ S j) (a : J → V)
    (c : J → Binary) (hc : c ≠ 0) :
    (PMF.uniformOfFintype (∀ j, S j)).toOuterMeasure
      {x | columnMap (fun j => a j + (x j).val) c = 0} ≤
      1 / (2 : ℝ≥0∞) ^ Module.finrank Binary S₀ :=
  coefficient_target_bound S S₀ hS a c hc 0

omit [Fintype T] in
/--
---
conclusion: Lax342547.AffineImages.dependence_bound
---
Every failure of column injectivity has a nonzero coefficient relation.
For each relation, its single image is uniform on an affine space whose
translation dimension is at least dim(S). Union over at most 2^|J|
coefficient vectors gives the stated bound.
-/
theorem dependence_bound [DecidableEq J] [FiniteDimensional Binary V]
    (S : J → Submodule Binary V) [∀ j, Fintype (S j)]
    (S₀ : Submodule Binary V) (hS : ∀ j, S₀ ≤ S j) (a : J → V) :
    (PMF.uniformOfFintype (∀ j, S j)).toOuterMeasure
      {x | ¬ Function.Injective (columnMap (fun j => a j + (x j).val))} ≤
      (2 : ℝ≥0∞) ^ Fintype.card J / 2 ^ Module.finrank Binary S₀ := by
  classical
  let p := PMF.uniformOfFintype (∀ j, S j)
  let R := {c : J → Binary // c ≠ 0}
  let A (c : R) := {x : ∀ j, S j | columnMap (fun j => a j + (x j).val) c.val = 0}
  have hsub : {x | ¬ Function.Injective (columnMap (fun j => a j + (x j).val))} ⊆
      ⋃ c : R, A c := by
    intro x hx
    change ¬ Function.Injective _ at hx
    rw [Function.Injective] at hx
    push Not at hx
    obtain ⟨c, d, he, hne⟩ := hx
    apply Set.mem_iUnion.mpr
    refine ⟨⟨c - d, sub_ne_zero.mpr hne⟩, ?_⟩
    change columnMap _ (c - d) = 0
    simp [map_sub, he]
  have hR : (Fintype.card R : ℝ≥0∞) ≤ (2 : ℝ≥0∞) ^ Fintype.card J := by
    have h := Fintype.card_subtype_le (fun c : J → Binary => c ≠ 0)
    have hc : Fintype.card (J → Binary) = 2 ^ Fintype.card J := by simp [Binary, ZMod.card]
    rw [hc] at h
    exact_mod_cast h
  calc
    _ ≤ p.toOuterMeasure (⋃ c : R, A c) := p.toOuterMeasure.mono hsub
    _ ≤ ∑ c : R, p.toOuterMeasure (A c) :=
      MeasureTheory.measure_iUnion_fintype_le p.toOuterMeasure _
    _ ≤ ∑ _c : R, 1 / (2 : ℝ≥0∞) ^ Module.finrank Binary S₀ :=
      Finset.sum_le_sum (fun c _ => coefficient_bound S S₀ hS a c.val c.property)
    _ = (Fintype.card R : ℝ≥0∞) / 2 ^ Module.finrank Binary S₀ := by simp [div_eq_mul_inv]
    _ ≤ _ := ENNReal.div_le_div_right hR _

omit [Fintype T] in
/--
---
conclusion: Lax342547.AffineImages.extension_dependence_bound
---
A new dependence extending an injective fixed map must have a nonzero
coefficient among the random columns. Its image equals a prescribed
negative old image. The affine single-image bound applies to each such
relation; union over old coefficients and nonzero new coefficients.
-/
theorem extension_dependence_bound {U : Type} [AddCommGroup U] [Module Binary U] [Fintype U]
    [DecidableEq J] [FiniteDimensional Binary V]
    (P : U →ₗ[Binary] V) (hP : Function.Injective P)
    (S : J → Submodule Binary V) [∀ j, Fintype (S j)]
    (S₀ : Submodule Binary V) (hS : ∀ j, S₀ ≤ S j) (a : J → V) :
    (PMF.uniformOfFintype (∀ j, S j)).toOuterMeasure
      {x | ¬ Function.Injective (fun z : U × (J → Binary) =>
        P z.1 + columnMap (fun j => a j + (x j).val) z.2)} ≤
      (Fintype.card U : ℝ≥0∞) * 2 ^ Fintype.card J / 2 ^ Module.finrank Binary S₀ := by
  classical
  let p := PMF.uniformOfFintype (∀ j, S j)
  let R := U × {c : J → Binary // c ≠ 0}
  let A (r : R) := {x : ∀ j, S j | columnMap (fun j => a j + (x j).val) r.2.val = -P r.1}
  have hsub : {x | ¬ Function.Injective (fun z : U × (J → Binary) =>
      P z.1 + columnMap (fun j => a j + (x j).val) z.2)} ⊆ ⋃ r : R, A r := by
    intro x hx
    change ¬ Function.Injective _ at hx
    rw [Function.Injective] at hx
    push Not at hx
    obtain ⟨⟨u, c⟩, ⟨v, d⟩, he, hne⟩ := hx
    have hcd : c ≠ d := by
      intro hcd
      apply hne
      have huv : u = v := hP (add_right_cancel (by simpa only [hcd] using he))
      exact Prod.ext huv hcd
    apply Set.mem_iUnion.mpr
    refine ⟨(u - v, ⟨c - d, sub_ne_zero.mpr hcd⟩), ?_⟩
    change columnMap (fun j => a j + (x j).val) (c - d) = -P (u - v)
    rw [map_sub, map_sub]
    have he' : P u + columnMap (fun j => a j + (x j).val) c =
        P v + columnMap (fun j => a j + (x j).val) d := he
    calc
      _ = (P u + columnMap (fun j => a j + (x j).val) c) -
          (P v + columnMap (fun j => a j + (x j).val) d) - (P u - P v) := by abel
      _ = _ := by rw [he']; simp
  have hR : (Fintype.card R : ℝ≥0∞) ≤ (Fintype.card U : ℝ≥0∞) * 2 ^ Fintype.card J := by
    have h := Fintype.card_subtype_le (fun c : J → Binary => c ≠ 0)
    have hc : Fintype.card (J → Binary) = 2 ^ Fintype.card J := by simp [Binary, ZMod.card]
    rw [hc] at h
    have h' : Fintype.card R ≤ Fintype.card U * 2 ^ Fintype.card J := by
      rw [Fintype.card_prod]
      exact Nat.mul_le_mul_left _ h
    exact_mod_cast h'
  calc
    _ ≤ p.toOuterMeasure (⋃ r : R, A r) := p.toOuterMeasure.mono hsub
    _ ≤ ∑ r : R, p.toOuterMeasure (A r) :=
      MeasureTheory.measure_iUnion_fintype_le p.toOuterMeasure _
    _ ≤ ∑ _r : R, 1 / (2 : ℝ≥0∞) ^ Module.finrank Binary S₀ :=
      Finset.sum_le_sum (fun r _ => coefficient_target_bound S S₀ hS a r.2.val r.2.property (-P r.1))
    _ = (Fintype.card R : ℝ≥0∞) / 2 ^ Module.finrank Binary S₀ := by simp [div_eq_mul_inv]
    _ ≤ _ := ENNReal.div_le_div_right hR _

end Lax342547Proofs.AffineImages
