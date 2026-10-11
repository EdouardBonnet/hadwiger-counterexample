import Lax342547.GramColumns
import Lax342547Proofs.PairedFrames
import Lax342547Proofs.FiniteUniform
import Lax342547.AffineImages
import Lax342547.FiniteLinearLaw
import Lax342547Proofs.MixerCompatibility

namespace Lax342547Proofs.GramColumns
open Lax342547.MomentSpace Lax342547.GramColumns
open scoped ENNReal
variable {I J N : Type} [Fintype I] [Fintype J] [Fintype N]

omit [Fintype J] in
theorem gram_surjective (A : Matrix N I Binary) (hA : Function.Injective A.mulVec) :
    Function.Surjective (gramMap (J := J) A) := by
  classical
  obtain ⟨U, hU⟩ := Lax342547Proofs.MixerCompatibility.exists_left_inverse A hA
  have ht : A.transpose * U.transpose = 1 := by simpa using congrArg Matrix.transpose hU
  intro G
  exact ⟨U.transpose * G, by simp [gramMap, ← Matrix.mul_assoc, ht]⟩

/--
---
conclusion: Lax342547.GramColumns.gram_uniform
---
A left inverse of the plus frame makes its transpose surjective. Left multiplication therefore sends a uniform minus matrix to the uniform Gram matrix.
-/
theorem gram_uniform [DecidableEq I] [DecidableEq J] [DecidableEq N] (A : Matrix N I Binary) (hA : Function.Injective A.mulVec) :
    (PMF.uniformOfFintype (Matrix N J Binary)).map (gramMap A) =
      PMF.uniformOfFintype (Matrix I J Binary) :=
  Lax342547.FiniteLinearLaw.uniform_image_of_surjective _ (gram_surjective A hA)

/--
---
conclusion: Lax342547.GramColumns.gram_probability
---
Each Gram value has exactly the reciprocal of the number of p-by-q binary matrices as its probability, for every injective plus frame.
-/
theorem gram_probability [DecidableEq I] [DecidableEq J] [DecidableEq N] (A : Matrix N I Binary) (hA : Function.Injective A.mulVec)
    (G : Matrix I J Binary) :
    (PMF.uniformOfFintype (Matrix N J Binary)).toOuterMeasure {B | A.transpose * B = G} =
      1 / (2 : ℝ≥0∞) ^ (Fintype.card I * Fintype.card J) := by
  have h := congrArg (fun p : PMF (Matrix I J Binary) => p.toOuterMeasure {G}) (Lax342547.GramColumns.gram_uniform A hA)
  rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_apply_singleton,
    PMF.uniformOfFintype_apply] at h
  change (PMF.uniformOfFintype (Matrix N J Binary)).toOuterMeasure {B | A.transpose * B = G} = _ at h
  rw [h]
  change (Fintype.card (I → J → Binary) : ℝ≥0∞)⁻¹ = _
  simp [Binary, ZMod.card, ← pow_mul, Nat.mul_comm]

noncomputable def fiberEquiv (A : Matrix N I Binary) (G : Matrix I J Binary)
    (B₀ : Matrix N J Binary) (h₀ : A.transpose * B₀ = G) :
    (J → LinearMap.ker A.transpose.mulVecLin) ≃ GramFiber A G where
  toFun x := ⟨fun n j => B₀ n j + (x j).val n, by
    ext i j
    have hx := congrFun (x j).property i
    have hb := congrFun (congrFun h₀ i) j
    change (∑ n, A n i * (B₀ n j + (x j).val n)) = G i j
    simp only [mul_add, Finset.sum_add_distrib]
    exact (congrArg₂ (· + ·) hb hx).trans (add_zero _)⟩
  invFun B j := ⟨fun n => B.val n j - B₀ n j, by
    ext i
    have hb := congrFun (congrFun B.property i) j
    have h₀' := congrFun (congrFun h₀ i) j
    change (∑ n, A n i * (B.val n j - B₀ n j)) = 0
    simp only [mul_sub, Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr (hb.trans h₀'.symm)⟩
  left_inv x := by ext j n; simp
  right_inv B := by ext n j; simp

/--
---
conclusion: Lax342547.GramColumns.conditional_failure
---
Translate the fixed Gram fiber into a product of plus-annihilator spaces. The affine-column dependence bound and rank-nullity give 2^(p+q-N), with no restriction on the Gram values.
-/
theorem conditional_failure [DecidableEq I] [DecidableEq J] [DecidableEq N]
    (A : Matrix N I Binary) (hA : Function.Injective A.mulVec) (G : Matrix I J Binary)
    [Nonempty (GramFiber A G)] :
    (PMF.uniformOfFintype (GramFiber A G)).toOuterMeasure {B | ¬ Function.Injective B.val.mulVec} ≤
      (2 : ℝ≥0∞) ^ (Fintype.card I + Fintype.card J) / 2 ^ Fintype.card N := by
  classical
  obtain ⟨B₀, h₀⟩ := gram_surjective A hA G
  let S := LinearMap.ker A.transpose.mulVecLin
  let a : J → (N → Binary) := fun j n => B₀ n j
  let e := fiberEquiv A G B₀ h₀
  have hmap := Lax342547Proofs.FiniteUniform.map_equiv e
  rw [← hmap, PMF.toOuterMeasure_map_apply]
  have he (x : J → S) : Lax342547.AffineImages.columnMap (fun j => a j + (x j).val) =
      (e x).val.mulVecLin := by
    apply LinearMap.ext
    intro c
    funext n
    change (∑ j, c j • (a j + (x j).val)) n =
      Matrix.mulVec (fun n j => B₀ n j + (x j).val n) c n
    simp [a, Matrix.mulVec, dotProduct, Finset.sum_apply, smul_eq_mul, mul_comm, mul_add]
  have hset : e ⁻¹' {B | ¬ Function.Injective B.val.mulVec} =
      {x : J → S | ¬ Function.Injective (Lax342547.AffineImages.columnMap (fun j => a j + (x j).val))} := by
    ext x
    rw [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_ofPred_eq, he]
    rfl
  rw [hset]
  have hb := Lax342547.AffineImages.dependence_bound (fun _ : J => S) S (fun _ => le_rfl) a
  have hd := A.transpose.mulVecLin.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (Lax342547Proofs.PairedFrames.transpose_surjective A hA),
    finrank_top, Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card] at hd
  change Fintype.card I + Module.finrank Binary S = Fintype.card N at hd
  calc
    _ ≤ (2 : ℝ≥0∞) ^ Fintype.card J / 2 ^ Module.finrank Binary S := hb
    _ = _ := by
      rw [← hd, pow_add, pow_add]
      exact (ENNReal.mul_div_mul_left _ _ (by simp) (by simp)).symm

/--
---
conclusion: Lax342547.GramColumns.extension_failure
---
Apply the affine extension-dependence estimate to the independent
annihilator columns of a fixed Gram fiber. When both old frames have
d columns and the channel has h, this is exactly 2^(2d+h-N), the
conditional channel-rank failure bound in Lemma 4.3(a).
-/
theorem extension_failure {K : Type} [Fintype K]
    [DecidableEq I] [DecidableEq J] [DecidableEq N]
    (P : Matrix N K Binary) (hP : Function.Injective P.mulVec)
    (A : Matrix N I Binary) (hA : Function.Injective A.mulVec) (G : Matrix I J Binary)
    [Nonempty (GramFiber A G)] :
    (PMF.uniformOfFintype (GramFiber A G)).toOuterMeasure
      {X | ¬ Function.Injective (fun z : (K → Binary) × (J → Binary) =>
        P.mulVec z.1 + X.val.mulVec z.2)} ≤
      (2 : ℝ≥0∞) ^ (Fintype.card K + Fintype.card I + Fintype.card J) / 2 ^ Fintype.card N := by
  classical
  obtain ⟨X₀, h₀⟩ := gram_surjective A hA G
  let S := LinearMap.ker A.transpose.mulVecLin
  let a : J → (N → Binary) := fun j n => X₀ n j
  let e := fiberEquiv A G X₀ h₀
  rw [← FiniteUniform.map_equiv e, PMF.toOuterMeasure_map_apply]
  have he (x : J → S) : Lax342547.AffineImages.columnMap (fun j => a j + (x j).val) =
      (e x).val.mulVecLin := by
    apply LinearMap.ext
    intro c
    funext n
    change (∑ j, c j • (a j + (x j).val)) n =
      Matrix.mulVec (fun n j => X₀ n j + (x j).val n) c n
    simp [a, Matrix.mulVec, dotProduct, Finset.sum_apply, smul_eq_mul, mul_comm, mul_add]
  have hset : e ⁻¹' {X | ¬ Function.Injective (fun z : (K → Binary) × (J → Binary) =>
      P.mulVec z.1 + X.val.mulVec z.2)} =
      {x : J → S | ¬ Function.Injective (fun z : (K → Binary) × (J → Binary) =>
        P.mulVec z.1 + Lax342547.AffineImages.columnMap (fun j => a j + (x j).val) z.2)} := by
    ext x
    rw [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_ofPred_eq, he]
    rfl
  rw [hset]
  have hb := Lax342547.AffineImages.extension_dependence_bound P.mulVecLin hP
    (fun _ : J => S) S (fun _ => le_rfl) a
  have hd := A.transpose.mulVecLin.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (PairedFrames.transpose_surjective A hA),
    finrank_top, Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card] at hd
  change Fintype.card I + Module.finrank Binary S = Fintype.card N at hd
  have hc : (Fintype.card (K → Binary) : ℝ≥0∞) = 2 ^ Fintype.card K := by
    simp [Binary, ZMod.card]
  rw [hc] at hb
  calc
    _ ≤ (2 : ℝ≥0∞) ^ Fintype.card K * 2 ^ Fintype.card J / 2 ^ Module.finrank Binary S := hb
    _ = _ := by
      rw [← hd]
      have he : Fintype.card K + Fintype.card I + Fintype.card J =
          Fintype.card I + (Fintype.card K + Fintype.card J) := by omega
      rw [he, pow_add, pow_add, pow_add]
      exact (ENNReal.mul_div_mul_left _ _ (by simp) (by simp)).symm

end Lax342547Proofs.GramColumns
