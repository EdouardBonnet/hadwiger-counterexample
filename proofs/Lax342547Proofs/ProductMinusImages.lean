import Lax342547.ProductMinusImages
import Lax342547Proofs.ProductImages
import Lax342547Proofs.ConditionalMinus

namespace Lax342547Proofs.ProductMinusImages

open Lax342547.MomentSpace Lax342547.ConditionalMinus Lax342547.ProductImages
open Lax342547.ProductMinusImages
open scoped ENNReal

variable {Draw B H T N : Type} [Fintype Draw] [Fintype B] [Fintype H] [Fintype T] [Fintype N]

omit [Fintype T] in
def commonSpace (P : Draw → Matrix N B Binary) (X : Draw → Matrix N H Binary) :
    Submodule Binary (N → Binary) :=
  LinearMap.ker (jointMatrix (fun i => Matrix.fromCols (P i) (X i))).transpose.mulVecLin

omit [Fintype Draw] [Fintype B] [Fintype H] [Fintype T] in
theorem common_space_le (P : Draw → Matrix N B Binary) (X : Draw → Matrix N H Binary)
    (j : Draw × (B ⊕ H)) :
    commonSpace P X ≤ ConditionalMinus.columnSpace (P j.1) (X j.1) j.2 := by
  intro v hv
  apply ConditionalMinus.common_space_le (P j.1) (X j.1) j.2
  change (Matrix.fromCols (P j.1) (X j.1)).transpose.mulVec v = 0
  funext k
  exact congrFun hv (j.1, k)

omit [Fintype T] in
theorem common_dimension (P : Draw → Matrix N B Binary) (X : Draw → Matrix N H Binary) :
    Fintype.card N - Fintype.card Draw * (Fintype.card B + Fintype.card H) ≤
      Module.finrank Binary (commonSpace P X) := by
  let L := (jointMatrix (fun i => Matrix.fromCols (P i) (X i))).transpose.mulVecLin
  have hd := L.finrank_range_add_finrank_ker
  have hr := LinearMap.finrank_le_finrank_of_injective (LinearMap.range L).subtype_injective
  rw [Module.finrank_fintype_fun_eq_card] at hd
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_prod, Fintype.card_sum] at hr
  change Module.finrank Binary (LinearMap.range L) + Module.finrank Binary (commonSpace P X) =
    Fintype.card N at hd
  omega

omit [Fintype T] in
noncomputable def columnsEquiv (E : Matrix B B Binary) (P : Draw → Matrix N B Binary)
    (X : Draw → Matrix N H Binary) (Q₀ : Draw → Matrix N B Binary)
    (h₀ : ∀ i, (Matrix.fromCols (P i) (X i)).transpose * Q₀ i = Matrix.fromRows E 0) :
    (∀ j : Draw × (B ⊕ H), ConditionalMinus.columnSpace (P j.1) (X j.1) j.2) ≃
      (∀ i, ColumnProduct E (P i) (X i)) :=
  let curry : (∀ j : Draw × (B ⊕ H), ConditionalMinus.columnSpace (P j.1) (X j.1) j.2) ≃
      (∀ i j, ConditionalMinus.columnSpace (P i) (X i) j) := {
    toFun := fun x i j => x (i, j)
    invFun := fun x j => x j.1 j.2
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  curry.trans (Equiv.piCongrRight (fun i => ConditionalMinus.columnEquiv E (P i) (X i) (Q₀ i) (h₀ i)))

/--
---
conclusion: Lax342547.ProductMinusImages.affine_image_bound
---
Reindex all affine columns into one independent family. Their common
translation space is the annihilator of every exposed plus frame and
has dimension at least N-k(d+h). The arbitrary-rank affine image theorem
then gives t times this dimension, including directions mixing draws.
-/
theorem affine_image_bound [DecidableEq Draw] [DecidableEq B] [DecidableEq H] [DecidableEq N]
    (E : Matrix B B Binary) (P : Draw → Matrix N B Binary) (X : Draw → Matrix N H Binary)
    (hPX : ∀ i, Function.Injective (Matrix.fromCols (P i) (X i)).mulVec)
    [∀ i, Nonempty (ColumnProduct E (P i) (X i))]
    (C : Matrix (Draw × (B ⊕ H)) T Binary) (hC : Function.Injective C.mulVec) (y : Matrix N T Binary) :
    (PMF.uniformOfFintype (∀ i, ColumnProduct E (P i) (X i))).map (images C) y ≤
      1 / (2 : ℝ≥0∞) ^ (Fintype.card T *
        (Fintype.card N - Fintype.card Draw * (Fintype.card B + Fintype.card H))) := by
  classical
  choose Q₀ h₀ using fun i => GramColumns.gram_surjective
    (Matrix.fromCols (P i) (X i)) (hPX i) (Matrix.fromRows E 0)
  let S (j : Draw × (B ⊕ H)) := ConditionalMinus.columnSpace (P j.1) (X j.1) j.2
  let a (j : Draw × (B ⊕ H)) : N → Binary :=
    Sum.elim (fun b n => Q₀ j.1 n b) (fun _ => 0) j.2
  let e := columnsEquiv E P X Q₀ h₀
  have hcols (x : ∀ j, S j) (j : Draw × (B ⊕ H)) :
      a j + (x j).val = fun n =>
        jointMatrix (fun i => Matrix.fromCols (e x i).1.val (e x i).2.val) n j := by
    rcases j with ⟨i, b | h⟩ <;> rfl
  have he (x : ∀ j, S j) :
      (fun t => ∑ j, C j t • a j) + Lax342547.AffineImages.evaluation S C x =
        fun t n => images C (e x) n t := by
    funext t
    change (∑ j, C j t • a j) + (∑ j, C j t • (x j).val) = _
    rw [← Finset.sum_add_distrib]
    simp_rw [← smul_add, hcols]
    funext n
    simp [images, Matrix.mul_apply, Finset.sum_apply, smul_eq_mul, mul_comm]
  have hu : (PMF.uniformOfFintype (∀ i, ColumnProduct E (P i) (X i))).map (images C) y =
      Lax342547.AffineImages.law S C a (fun t n => y n t) := by
    rw [← FiniteUniform.map_equiv e, PMF.map_comp]
    rw [← PMF.toOuterMeasure_apply_singleton, Lax342547.AffineImages.law,
      ← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_map_apply]
    congr 1
    ext x
    change images C (e x) = y ↔
      (fun t => ∑ j, C j t • a j) + Lax342547.AffineImages.evaluation S C x = (fun t n => y n t)
    rw [he]
    constructor
    · intro h
      exact congrArg Matrix.transpose h
    · intro h
      exact Matrix.transpose_injective h
  rw [hu]
  calc
    _ ≤ 1 / (2 : ℝ≥0∞) ^ (Fintype.card T * Module.finrank Binary (commonSpace P X)) :=
      AffineImages.image_bound S (commonSpace P X) (common_space_le P X) C hC a _
    _ ≤ _ := ENNReal.div_le_div_left
      (pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left _ (common_dimension P X))) _

/--
---
conclusion: Lax342547.ProductMinusImages.completion_image_bound
---
Each exposed plus frame leaves a minus injectivity conditioning of cost
at most two. Product density and pushforward preserve the resulting
2^k factor on the joint affine image estimate.
-/
theorem completion_image_bound [DecidableEq Draw] [DecidableEq B] [DecidableEq H] [DecidableEq N]
    (E : Matrix B B Binary) (P : Draw → Matrix N B Binary) (X : Draw → Matrix N H Binary)
    (hPX : ∀ i, Function.Injective (Matrix.fromCols (P i) (X i)).mulVec)
    [∀ i, Nonempty (ColumnProduct E (P i) (X i))] [∀ i, Nonempty (Completion E (P i) (X i))]
    (hN : 2 * (Fintype.card B + Fintype.card H) + 1 ≤ Fintype.card N)
    (C : Matrix (Draw × (B ⊕ H)) T Binary) (hC : Function.Injective C.mulVec) (y : Matrix N T Binary) :
    (PMF.uniformOfFintype (∀ i, Completion E (P i) (X i))).map
      (fun z => images C (fun i => (z i).val)) y ≤
      (2 : ℝ≥0∞) ^ Fintype.card Draw / 2 ^ (Fintype.card T *
        (Fintype.card N - Fintype.card Draw * (Fintype.card B + Fintype.card H))) := by
  have hd (i : Draw) (z : ColumnProduct E (P i) (X i)) :
      (PMF.uniformOfFintype (Completion E (P i) (X i))).map Subtype.val z ≤
        2 * PMF.uniformOfFintype (ColumnProduct E (P i) (X i)) z := by
    rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply,
      ← PMF.toOuterMeasure_apply_singleton]
    exact ConditionalMinus.completion_event_bound E (P i) (X i) (hPX i) hN {z}
  let p := (PMF.uniformOfFintype (∀ i, Completion E (P i) (X i))).map (fun z i => (z i).val)
  let q := PMF.uniformOfFintype (∀ i, ColumnProduct E (P i) (X i))
  have hp (z : ∀ i, ColumnProduct E (P i) (X i)) : p z ≤ (2 : ℝ≥0∞) ^ Fintype.card Draw * q z := by
    simpa only [Finset.prod_const, Finset.card_univ] using
      FiniteUniform.map_pi_density (fun i => (Subtype.val : Completion E (P i) (X i) → _))
        (fun _ => 2) hd z
  have hb := FiniteProbability.map_density p q _ hp (images C) y
  change ((PMF.uniformOfFintype (∀ i, Completion E (P i) (X i))).map _).map _ y ≤ _ at hb
  rw [PMF.map_comp] at hb
  calc
    _ ≤ (2 : ℝ≥0∞) ^ Fintype.card Draw * q.map (images C) y := hb
    _ ≤ (2 : ℝ≥0∞) ^ Fintype.card Draw *
        (1 / 2 ^ (Fintype.card T * (Fintype.card N - Fintype.card Draw * (Fintype.card B + Fintype.card H)))) :=
      mul_le_mul_of_nonneg_left (affine_image_bound E P X hPX C hC y) zero_le
    _ = _ := by rw [mul_one_div]

end Lax342547Proofs.ProductMinusImages
