import Lax342547.ProductImages
import Lax342547Proofs.InjectiveFrames

namespace Lax342547Proofs.ProductImages

open Lax342547.MomentSpace Lax342547.FrameSymmetry Lax342547.RawFrames
open Lax342547.ProductImages
open scoped ENNReal

/--
---
conclusion: Lax342547.ProductImages.rank_restriction
---
Choose a basis of the nominal coefficient image and lift it through the
coefficient map. Right multiplication by its lift extracts a full-rank
tuple of exactly the original nominal rank from any tested tuple.
-/
theorem rank_restriction {I T : Type} [Fintype I] [Fintype T]
    (C : Matrix I T Binary) :
    ∃ D : Matrix T (Fin C.rank) Binary, Function.Injective (C * D).mulVec := by
  classical
  let f := C.mulVecLin
  let S := LinearMap.range f
  let e := (Module.finBasis Binary S).equivFun
  obtain ⟨q, hq⟩ := f.rangeRestrict.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr f.surjective_rangeRestrict)
  let d := q.comp e.symm.toLinearMap
  have he : f.comp d = S.subtype.comp e.symm.toLinearMap := by
    calc
      _ = S.subtype.comp ((f.rangeRestrict.comp q).comp e.symm.toLinearMap) := rfl
      _ = _ := by rw [hq, LinearMap.id_comp]
  have hm : C * d.toMatrix' = (S.subtype.comp e.symm.toLinearMap).toMatrix' := by
    calc
      _ = f.toMatrix' * d.toMatrix' := by rw [PairedFrames.toMatrix_mulVecLin]
      _ = _ := by rw [← LinearMap.toMatrix'_comp, he]
  refine ⟨d.toMatrix', ?_⟩
  change Function.Injective ((C * d.toMatrix') : Matrix I (Fin (Module.finrank Binary S)) Binary).mulVec
  rw [hm]
  intro x y h
  apply e.symm.injective
  apply Subtype.val_injective
  simpa using h

/--
---
conclusion: Lax342547.ProductImages.right_uniform
---
A left inverse of the coefficient matrix makes right multiplication
surjective, so it sends the uniform column matrix to a uniform image.
-/
theorem right_uniform {I T N : Type} [Fintype I] [Fintype T] [Fintype N]
    [DecidableEq I] [DecidableEq T] [DecidableEq N]
    (C : Matrix I T Binary) (hC : Function.Injective C.mulVec) :
    (PMF.uniformOfFintype (Matrix N I Binary)).map (fun A => A * C) =
      PMF.uniformOfFintype (Matrix N T Binary) := by
  apply FiniteLinearLaw.uniform_image_of_surjective (rightMap C)
  obtain ⟨U, hU⟩ := MixerCompatibility.exists_left_inverse C hC
  intro y
  exact ⟨y * U, by simp only [rightMap, LinearMap.coe_mk, AddHom.coe_mk,
    Matrix.mul_assoc, hU, Matrix.mul_one]⟩

/--
---
conclusion: Lax342547.ProductImages.joint_uniform
---
Reindex all independently sampled columns by the direct sum over draws.
Injectivity of the nominal coefficient tuple then gives the exact
uniform law, even when every direction mixes several source frames.
-/
theorem joint_uniform {Draw I T N : Type} [Fintype Draw] [Fintype I] [Fintype T] [Fintype N]
    [DecidableEq Draw] [DecidableEq I] [DecidableEq T] [DecidableEq N]
    (C : Matrix (Draw × I) T Binary) (hC : Function.Injective C.mulVec) :
    (PMF.uniformOfFintype (Draw → Matrix N I Binary)).map (fun A => jointMatrix A * C) =
      PMF.uniformOfFintype (Matrix N T Binary) := by
  rw [← right_uniform C hC, ← FiniteUniform.map_equiv (jointEquiv (Draw := Draw) (I := I) (N := N)),
    PMF.map_comp]
  rfl

/--
---
conclusion: Lax342547.ProductImages.injective_image_bound
---
Each source-frame injectivity conditioning costs at most two. The
product density is therefore at most 2^(number of draws); pushing it
through the joint image map preserves this bound against the exact
uniform image law, with no restriction on the tuple rank.
-/
theorem injective_image_bound {Draw I T N : Type}
    [Fintype Draw] [Fintype I] [Fintype T] [Fintype N]
    [DecidableEq Draw] [DecidableEq I] [DecidableEq T] [DecidableEq N]
    [Nonempty (Injection I N)] (hN : Fintype.card I + 1 ≤ Fintype.card N)
    (C : Matrix (Draw × I) T Binary) (hC : Function.Injective C.mulVec) (y : Matrix N T Binary) :
    (PMF.uniformOfFintype (Draw → Injection I N)).map
      (fun A => jointMatrix (fun i => (A i).val) * C) y ≤
      (2 : ℝ≥0∞) ^ Fintype.card Draw / 2 ^ (Fintype.card N * Fintype.card T) := by
  have hd (M : Matrix N I Binary) : (PMF.uniformOfFintype (Injection I N)).map Subtype.val M ≤
      2 * PMF.uniformOfFintype (Matrix N I Binary) M := by
    rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply,
      ← PMF.toOuterMeasure_apply_singleton]
    exact InjectiveFrames.injection_event_bound hN {M}
  let p := (PMF.uniformOfFintype (Draw → Injection I N)).map (fun A i => (A i).val)
  let q := PMF.uniformOfFintype (Draw → Matrix N I Binary)
  have hp (A : Draw → Matrix N I Binary) : p A ≤ (2 : ℝ≥0∞) ^ Fintype.card Draw * q A := by
    simpa only [Finset.prod_const, Finset.card_univ] using
      FiniteUniform.map_pi_density (fun _ : Draw => (Subtype.val : Injection I N → Matrix N I Binary))
        (fun _ => 2) (fun _ M => hd M) A
  have hb := FiniteProbability.map_density p q _ hp (fun A => jointMatrix A * C) y
  change ((PMF.uniformOfFintype (Draw → Injection I N)).map _).map _ y ≤ _ at hb
  rw [PMF.map_comp] at hb
  change _ ≤ (2 : ℝ≥0∞) ^ Fintype.card Draw *
    (PMF.uniformOfFintype (Draw → Matrix N I Binary)).map (fun A => jointMatrix A * C) y at hb
  rw [joint_uniform C hC, PMF.uniformOfFintype_apply] at hb
  have hc : Fintype.card (Matrix N T Binary) = 2 ^ (Fintype.card N * Fintype.card T) := by
    rw [← Nat.card_eq_fintype_card]
    change Nat.card (N → T → Binary) = _
    rw [Nat.card_fun, Nat.card_fun]
    simp [Nat.card_eq_fintype_card, Binary, ZMod.card, ← pow_mul, Nat.mul_comm]
  simpa only [Function.comp_def, hc, Nat.cast_pow, Nat.cast_ofNat, div_eq_mul_inv] using hb

/--
---
conclusion: Lax342547.ProductImages.raw_plus_image_bound
---
The combined plus-frame marginal is uniform independently at every raw
draw. The joint nominal-image estimate therefore applies to the actual
raw law, including directions that mix both endpoints of a unit.
-/
theorem raw_plus_image_bound {Draw B H T N : Type}
    [Fintype Draw] [Fintype B] [Fintype H] [Fintype T] [Fintype N]
    [DecidableEq Draw] [DecidableEq B] [DecidableEq H] [DecidableEq T] [DecidableEq N]
    {E : Matrix B B Binary} [Nonempty (Frame B H N E)]
    (hN : Fintype.card B + Fintype.card H + 1 ≤ Fintype.card N)
    (C : Matrix (Draw × (B ⊕ H)) T Binary) (hC : Function.Injective C.mulVec)
    (y : Matrix N T Binary) :
    (PMF.uniformOfFintype (Draw → Frame B H N E)).map
      (fun o => jointMatrix (fun i => (plus (o i)).val) * C) y ≤
      (2 : ℝ≥0∞) ^ Fintype.card Draw / 2 ^ (Fintype.card N * Fintype.card T) := by
  let : Nonempty (Injection (B ⊕ H) N) := ⟨plus (Classical.choice (inferInstance : Nonempty (Frame B H N E)))⟩
  have hm : (PMF.uniformOfFintype (Draw → Frame B H N E)).map (fun o i => plus (o i)) =
      PMF.uniformOfFintype (Draw → Injection (B ⊕ H) N) := by
    ext A
    rw [FiniteUniform.map_fun_apply, FiniteUniform.uniform_pi_apply]
    apply Finset.prod_congr rfl
    intro i _
    rw [FrameSymmetry.plus_uniform]
  have hb := injective_image_bound (by simpa only [Fintype.card_sum] using hN) C hC y
  rw [← hm, PMF.map_comp] at hb
  exact hb

end Lax342547Proofs.ProductImages
