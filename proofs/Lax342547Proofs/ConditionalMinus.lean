import Lax342547.ConditionalMinus
import Lax342547Proofs.GramColumns
import Lax342547Proofs.GramNormalization

namespace Lax342547Proofs.ConditionalMinus

open Lax342547.MomentSpace Lax342547.RawFrames Lax342547.GramColumns
open Lax342547.ConditionalMinus
open scoped ENNReal

variable {B H N : Type} [Fintype B] [Fintype H] [Fintype N]

/--
---
conclusion: Lax342547.ConditionalMinus.conditional_uniform
---
The explicit completion equivalence shows that, at a fixed plus frame,
the uniform raw conditional law is the independent affine-column product
restricted only by full minus injectivity.
-/
theorem conditional_uniform {E : Matrix B B Binary} {P : Matrix N B Binary} {X : Matrix N H Binary}
    (hPX : Function.Injective (Matrix.fromCols P X).mulVec)
    [Nonempty (Fiber E P X)] [Nonempty (Completion E P X)] :
    (PMF.uniformOfFintype (Fiber E P X)).map columns = PMF.uniformOfFintype (Completion E P X) :=
  FiniteUniform.map_equiv (completionEquiv hPX)

def columnSpace (P : Matrix N B Binary) (X : Matrix N H Binary) :
    B ⊕ H → Submodule Binary (N → Binary) :=
  Sum.elim (fun _ => LinearMap.ker (Matrix.fromCols P X).transpose.mulVecLin)
    (fun _ => LinearMap.ker P.transpose.mulVecLin)

noncomputable def columnEquiv (E : Matrix B B Binary) (P : Matrix N B Binary) (X : Matrix N H Binary)
    (Q₀ : Matrix N B Binary) (h₀ : (Matrix.fromCols P X).transpose * Q₀ = Matrix.fromRows E 0) :
    (∀ j, columnSpace P X j) ≃ ColumnProduct E P X :=
  (Equiv.sumPiEquivProdPi (fun j => columnSpace P X j)).trans
    (Equiv.prodCongr (GramColumns.fiberEquiv (Matrix.fromCols P X) (Matrix.fromRows E 0) Q₀ h₀)
      (GramColumns.fiberEquiv P 0 0 (Matrix.mul_zero _)))

omit [Fintype B] [Fintype H] in
theorem common_space_le (P : Matrix N B Binary) (X : Matrix N H Binary) (j : B ⊕ H) :
    LinearMap.ker (Matrix.fromCols P X).transpose.mulVecLin ≤ columnSpace P X j := by
  cases j with
  | inl b => exact le_rfl
  | inr h =>
    intro v hv
    change P.transpose.mulVec v = 0
    funext b
    exact congrFun hv (Sum.inl b)

/--
---
conclusion: Lax342547.ConditionalMinus.rank_failure
---
Both affine column families contain the annihilator of [P,X], whose
dimension is N-d-h. Every nonzero minus relation therefore vanishes
with probability at most 2^(-(N-d-h)); union over 2^(d+h) relations.
-/
theorem rank_failure [DecidableEq B] [DecidableEq H] [DecidableEq N]
    (E : Matrix B B Binary) (P : Matrix N B Binary) (X : Matrix N H Binary)
    (hPX : Function.Injective (Matrix.fromCols P X).mulVec) [Nonempty (ColumnProduct E P X)] :
    (PMF.uniformOfFintype (ColumnProduct E P X)).toOuterMeasure {z | ¬ Good z} ≤
      (2 : ℝ≥0∞) ^ (2 * (Fintype.card B + Fintype.card H)) / 2 ^ Fintype.card N := by
  classical
  obtain ⟨Q₀, h₀⟩ := GramColumns.gram_surjective (Matrix.fromCols P X) hPX (Matrix.fromRows E 0)
  let S := LinearMap.ker (Matrix.fromCols P X).transpose.mulVecLin
  let a : B ⊕ H → (N → Binary) := Sum.elim (fun b n => Q₀ n b) (fun _ => 0)
  let e := columnEquiv E P X Q₀ h₀
  have hcols (x : ∀ j, columnSpace P X j) (j : B ⊕ H) :
      a j + (x j).val = fun n => Matrix.fromCols (e x).1.val (e x).2.val n j := by
    cases j <;> rfl
  have he (x : ∀ j, columnSpace P X j) :
      Lax342547.AffineImages.columnMap (fun j => a j + (x j).val) =
        (Matrix.fromCols (e x).1.val (e x).2.val).mulVecLin := by
    apply LinearMap.ext
    intro c
    funext n
    simp only [Lax342547.AffineImages.columnMap, LinearMap.coe_mk, AddHom.coe_mk,
      hcols, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVecLin_apply,
      Matrix.mulVec, dotProduct, mul_comm]
  rw [← FiniteUniform.map_equiv e, PMF.toOuterMeasure_map_apply]
  have hset : e ⁻¹' {z | ¬ Good z} =
      {x : ∀ j, columnSpace P X j |
        ¬ Function.Injective (Lax342547.AffineImages.columnMap (fun j => a j + (x j).val))} := by
    ext x
    rw [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_ofPred_eq, he]
    exact not_congr (combined_injective_iff (e x).1.val (e x).2.val).symm
  rw [hset]
  have hb := AffineImages.dependence_bound (columnSpace P X) S (common_space_le P X) a
  have hd := (Matrix.fromCols P X).transpose.mulVecLin.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (PairedFrames.transpose_surjective (Matrix.fromCols P X) hPX),
    finrank_top, Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card,
    Fintype.card_sum] at hd
  change Fintype.card B + Fintype.card H + Module.finrank Binary S = Fintype.card N at hd
  rw [Fintype.card_sum] at hb
  calc
    _ ≤ (2 : ℝ≥0∞) ^ (Fintype.card B + Fintype.card H) / 2 ^ Module.finrank Binary S := hb
    _ = _ := by
      rw [← hd, two_mul,
        pow_add (2 : ℝ≥0∞) (Fintype.card B + Fintype.card H) (Fintype.card B + Fintype.card H),
        pow_add (2 : ℝ≥0∞) (Fintype.card B + Fintype.card H) (Module.finrank Binary S)]
      exact (ENNReal.mul_div_mul_left _ _
        (show (2 : ℝ≥0∞) ^ (Fintype.card B + Fintype.card H) ≠ 0 by simp) (by simp)).symm

/--
---
conclusion: Lax342547.ConditionalMinus.raw_conditioning
---
The uniform-completion law is the actual filtered and renormalized raw
law at fixed P,X, after observing Q,Y. Thus the affine conditional law
is identified on the original reference probability space.
-/
theorem raw_conditioning {E : Matrix B B Binary} {P : Matrix N B Binary} {X : Matrix N H Binary}
    (hPX : Function.Injective (Matrix.fromCols P X).mulVec)
    [Nonempty (Frame B H N E)] [Nonempty (Fiber E P X)] [Nonempty (Completion E P X)]
    (h : ∃ F ∈ {F : Frame B H N E | F.P = P ∧ F.X = X},
      F ∈ (PMF.uniformOfFintype (Frame B H N E)).support) :
    ((PMF.uniformOfFintype (Frame B H N E)).filter {F | F.P = P ∧ F.X = X} h).map
      (fun F => (F.Q, F.Y)) =
    (PMF.uniformOfFintype (Completion E P X)).map (fun z => (z.val.1.val, z.val.2.val)) := by
  classical
  let : Nonempty {F : Frame B H N E | F.P = P ∧ F.X = X} := by
    obtain ⟨F, hF, _⟩ := h
    exact ⟨⟨F, hF⟩⟩
  rw [FiniteUniform.filter_uniform (α := Frame B H N E) {F | F.P = P ∧ F.X = X} h]
  rw [← conditional_uniform hPX, PMF.map_comp, PMF.map_comp]
  rfl

/--
---
conclusion: Lax342547.ConditionalMinus.completion_event_bound
---
One dimension beyond twice the full-frame size makes the failure bound
at most one half. Conditioning the affine column product on full minus
injectivity therefore increases any event probability by at most two.
-/
theorem completion_event_bound [DecidableEq B] [DecidableEq H] [DecidableEq N]
    (E : Matrix B B Binary) (P : Matrix N B Binary) (X : Matrix N H Binary)
    (hPX : Function.Injective (Matrix.fromCols P X).mulVec)
    [Nonempty (ColumnProduct E P X)] [Nonempty (Completion E P X)]
    (hN : 2 * (Fintype.card B + Fintype.card H) + 1 ≤ Fintype.card N)
    (S : Set (ColumnProduct E P X)) :
    (PMF.uniformOfFintype (Completion E P X)).toOuterMeasure {z | z.val ∈ S} ≤
      2 * (PMF.uniformOfFintype (ColumnProduct E P X)).toOuterMeasure S := by
  have hb := (rank_failure E P X hPX).trans (GramNormalization.power_ratio_le_half _ _ hN)
  have hm := FiniteProbability.event_ge_of_compl_le (PMF.uniformOfFintype (ColumnProduct E P X))
    {z | Good z} (1 / 2) hb
  have hc : 1 ≤ 2 * (PMF.uniformOfFintype (ColumnProduct E P X)).toOuterMeasure {z | Good z} := by
    have hhalf : (1 : ℝ≥0∞) - 1 / 2 = 1 / 2 := by norm_num
    rw [hhalf] at hm
    calc
      (1 : ℝ≥0∞) = 2 * (1 / 2) := by
        rw [one_div, ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]
      _ ≤ _ := mul_le_mul_of_nonneg_left hm zero_le
  exact @FiniteProbability.uniform_subtype_bound_factor (ColumnProduct E P X) inferInstance inferInstance
    {z | Good z} S (inferInstance : Fintype (Completion E P X))
    (inferInstance : Nonempty (Completion E P X)) 2 hc

end Lax342547Proofs.ConditionalMinus
