import Lax342547.InjectiveFrames
import Lax342547Proofs.GramNormalization
import Lax342547Proofs.FrameSymmetry

namespace Lax342547Proofs.InjectiveFrames

open Lax342547.MomentSpace Lax342547.FrameSymmetry
open scoped ENNReal

/--
---
conclusion: Lax342547.InjectiveFrames.injective_mass_half
---
The independent-column failure bound is at most one half once the
ambient dimension exceeds the number of columns by one.
-/
theorem injective_mass_half {H N : Type} [Fintype H] [Fintype N]
    [DecidableEq H] [DecidableEq N] (hN : Fintype.card H + 1 ≤ Fintype.card N) :
    (1 / 2 : ℝ≥0∞) ≤ (PMF.uniformOfFintype (Matrix N H Binary)).toOuterMeasure
      {A | Function.Injective A.mulVec} := by
  have hb := (GramNormalization.column_failure (J := H) (N := N)).trans
    (GramNormalization.power_ratio_le_half _ _ hN)
  have h := FiniteProbability.event_ge_of_compl_le (PMF.uniformOfFintype (Matrix N H Binary))
    {A | Function.Injective A.mulVec} (1 / 2) hb
  norm_num at h ⊢
  exact h

/--
---
conclusion: Lax342547.InjectiveFrames.injection_event_bound
---
The uniform injective-frame law is uniform conditioning on an event of
mass at least one half. Every event therefore costs at most twice its
independent-column probability.
-/
theorem injection_event_bound {H N : Type} [Fintype H] [Fintype N]
    [DecidableEq H] [DecidableEq N] [Nonempty (Injection H N)]
    (hN : Fintype.card H + 1 ≤ Fintype.card N) (S : Set (Matrix N H Binary)) :
    (PMF.uniformOfFintype (Injection H N)).toOuterMeasure {A | A.val ∈ S} ≤
      2 * (PMF.uniformOfFintype (Matrix N H Binary)).toOuterMeasure S := by
  have hc : 1 ≤ 2 * (PMF.uniformOfFintype (Matrix N H Binary)).toOuterMeasure
      {A | Function.Injective A.mulVec} := by
    calc
      (1 : ℝ≥0∞) = 2 * (1 / 2) := by
        rw [one_div, ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]
      _ ≤ _ := mul_le_mul_of_nonneg_left (injective_mass_half hN) zero_le
  exact @FiniteProbability.uniform_subtype_bound_factor (Matrix N H Binary) inferInstance inferInstance
    {A | Function.Injective A.mulVec} S (inferInstance : Fintype (Injection H N))
    (inferInstance : Nonempty (Injection H N)) 2 hc

/--
---
conclusion: Lax342547.InjectiveFrames.transpose_uniform
---
Transpose evaluation on an independent nominal tuple is the transpose of
its uniform Gram observation, hence exactly a uniform rectangular matrix.
-/
theorem transpose_uniform {I H N : Type} [Fintype I] [Fintype H] [Fintype N]
    [DecidableEq I] [DecidableEq H] [DecidableEq N]
    (D : Matrix N I Binary) (hD : Function.Injective D.mulVec) :
    (PMF.uniformOfFintype (Matrix N H Binary)).map (fun X => X.transpose * D) =
      PMF.uniformOfFintype (Matrix H I Binary) := by
  let e : Matrix I H Binary ≃ Matrix H I Binary :=
    ⟨Matrix.transpose, Matrix.transpose, Matrix.transpose_transpose, Matrix.transpose_transpose⟩
  have h := congrArg (PMF.map e) (GramColumns.gram_uniform (J := H) D hD)
  rw [PMF.map_comp, FiniteUniform.map_equiv e] at h
  simpa [e, Function.comp_def, Lax342547.GramColumns.gramMap, Matrix.transpose_mul] using h

/--
---
conclusion: Lax342547.InjectiveFrames.transpose_failure
---
Before injectivity conditioning, transpose evaluation is a uniform
h-by-q matrix, whose column-rank failure is at most 2^(q-h). Conditioning
the channel frame itself to be injective multiplies this by at most two.
-/
theorem transpose_failure {I H N : Type} [Fintype I] [Fintype H] [Fintype N]
    [DecidableEq I] [DecidableEq H] [DecidableEq N] [Nonempty (Injection H N)]
    (D : Matrix N I Binary) (hD : Function.Injective D.mulVec)
    (hN : Fintype.card H + 1 ≤ Fintype.card N) :
    (PMF.uniformOfFintype (Injection H N)).toOuterMeasure
      {X | ¬ Function.Injective (X.val.transpose * D).mulVec} ≤
      (2 : ℝ≥0∞) ^ (Fintype.card I + 1) / 2 ^ Fintype.card H := by
  have hb := GramNormalization.column_failure (J := I) (N := H)
  rw [← transpose_uniform D hD, PMF.toOuterMeasure_map_apply] at hb
  calc
    _ ≤ 2 * (PMF.uniformOfFintype (Matrix N H Binary)).toOuterMeasure
        {X | ¬ Function.Injective (X.transpose * D).mulVec} := injection_event_bound hN _
    _ ≤ 2 * ((2 : ℝ≥0∞) ^ Fintype.card I / 2 ^ Fintype.card H) :=
      mul_le_mul_of_nonneg_left hb zero_le
    _ = _ := by rw [pow_succ, ← mul_div_assoc, mul_comm 2]

/--
---
conclusion: Lax342547.InjectiveFrames.raw_transpose_failures
---
The two unconditional channel marginals of the actual raw-frame law
are uniform injective frames, so the transpose estimate applies to each.
-/
theorem raw_transpose_failures {B I H N : Type}
    [Fintype B] [Fintype I] [Fintype H] [Fintype N]
    [DecidableEq I] [DecidableEq H] [DecidableEq N]
    {E : Matrix B B Binary} [Nonempty (Lax342547.RawFrames.Frame B H N E)]
    (D : Matrix N I Binary) (hD : Function.Injective D.mulVec)
    (hN : Fintype.card H + 1 ≤ Fintype.card N) :
    (PMF.uniformOfFintype (Lax342547.RawFrames.Frame B H N E)).toOuterMeasure
        {F | ¬ Function.Injective (F.X.transpose * D).mulVec} ≤
        (2 : ℝ≥0∞) ^ (Fintype.card I + 1) / 2 ^ Fintype.card H ∧
    (PMF.uniformOfFintype (Lax342547.RawFrames.Frame B H N E)).toOuterMeasure
        {F | ¬ Function.Injective (F.Y.transpose * D).mulVec} ≤
        (2 : ℝ≥0∞) ^ (Fintype.card I + 1) / 2 ^ Fintype.card H := by
  let : Nonempty (Injection H N) :=
    ⟨plusChannel (Classical.choice (inferInstance : Nonempty (Lax342547.RawFrames.Frame B H N E)))⟩
  have hX := transpose_failure D hD hN
  have hY := transpose_failure D hD hN
  rw [← FrameSymmetry.plusChannel_uniform (E := E), PMF.toOuterMeasure_map_apply] at hX
  rw [← FrameSymmetry.minusChannel_uniform (E := E), PMF.toOuterMeasure_map_apply] at hY
  exact ⟨hX, hY⟩

end Lax342547Proofs.InjectiveFrames
