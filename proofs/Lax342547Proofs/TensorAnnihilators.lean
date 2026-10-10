import Lax342547.TensorAnnihilators
import Lax342547Proofs.QuotientRank
import Lax342547Proofs.SelectedMoments

namespace Lax342547Proofs.TensorAnnihilators

open Lax342547.MomentSpace Lax342547.ConcreteGeometry
open Lax342547.BaseMoments Lax342547.SelectedMoments Lax342547.TensorAnnihilators
open Matrix

set_option backward.isDefEq.respectTransparency false

variable {I : Type} [Fintype I] [DecidableEq I]

theorem functional_coordinates (φ : Module.Dual Binary (I → Binary)) (v : I → Binary) :
    φ v = ∑ i, v i * dualCoordinates φ i := by
  conv_lhs => rw [pi_eq_sum_univ' v]
  simp [dualCoordinates]

theorem coordinates_surjective :
    Function.Surjective (dualCoordinates (I := I)) := by
  intro v
  refine ⟨dotProductBilin Binary Binary v, ?_⟩
  ext i
  change dotProduct v (Pi.single i 1) = v i
  simp [dotProduct_single]

theorem pure_rank_one (M : Matrix I I Binary)
    (S T : Submodule Binary (I → Binary))
    (φ ψ : Module.Dual Binary (I → Binary))
    (hφ : S ≤ LinearMap.ker φ) (hψ : T ≤ LinearMap.ker ψ) :
    pureContraction S T ((S.liftQ φ hφ).smulRight (T.liftQ ψ hψ)) M =
      φ (M.mulVecLin (dualCoordinates ψ)) := by
  rw [functional_coordinates]
  simp only [pureContraction, matrixPair, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.BilinForm.toMatrix'_apply, LinearMap.compl₁₂_apply,
    LinearMap.smulRight_apply, Submodule.liftQ_apply, Submodule.mkQ_apply,
    smul_eq_mul, matrixEntry, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp [dualCoordinates, mul_comm, mul_left_comm]
  left
  apply congrArg₂ (· * ·)
  all_goals
    congr 1
    funext a
    simp [Pi.single_apply]

theorem annihilator_contraction (M : Matrix I I Binary)
    (S T : Submodule Binary (I → Binary)) (h : PureAnnihilates M S T)
    (φ ψ : Module.Dual Binary (I → Binary))
    (hφ : S ≤ LinearMap.ker φ) (hψ : T ≤ LinearMap.ker ψ) :
    φ (M.mulVecLin (dualCoordinates ψ)) = 0 := by
  rw [← pure_rank_one M S T φ ψ hφ hψ]
  exact h _

/--
---
conclusion: Lax342547.TensorAnnihilators.pure_rank
---
Test every product of quotient functionals. Double annihilation puts the
contracted tensor in the left subspace; the two-quotient rank theorem
then bounds its rank. Coordinate duality preserves the original rank.
-/
theorem pure_rank (M : Matrix I I Binary) (S T : Submodule Binary (I → Binary))
    (h : PureAnnihilates M S T) :
    M.rank ≤ Module.finrank Binary S + Module.finrank Binary T := by
  let f := M.mulVecLin.comp (dualCoordinates (I := I))
  have hc : S.mkQ.comp (f.comp T.mkQ.dualMap) = 0 := by
    ext ψ
    apply (Submodule.Quotient.mk_eq_zero S).mpr
    rw [← Subspace.dualAnnihilator_dualCoannihilator_eq (W := S)]
    apply (Submodule.mem_dualCoannihilator _).mpr
    intro φ hφ
    apply annihilator_contraction M S T h φ (T.mkQ.dualMap ψ)
    · intro v hv
      exact (Submodule.mem_dualAnnihilator φ).mp hφ v hv
    · intro v hv
      change ψ (T.mkQ v) = 0
      have hvzero : T.mkQ v = 0 := (Submodule.Quotient.mk_eq_zero T).mpr hv
      rw [hvzero, map_zero]
  have hr := QuotientRank.killed_quotients_rank f S T hc
  have heq : LinearMap.range f = LinearMap.range M.mulVecLin := by
    rw [LinearMap.range_comp, LinearMap.range_eq_top.mpr coordinates_surjective,
      Submodule.map_top]
  rw [heq] at hr
  exact hr

/--
---
conclusion: Lax342547.TensorAnnihilators.pure_sandwich
---
Every row of each quotient-killing matrix is a quotient functional.
Their product test is precisely the corresponding sandwich entry.
-/
theorem pure_sandwich {I P Q : Type} [Fintype I] [Fintype P] [Fintype Q]
    [DecidableEq I]
    (M : Matrix I I Binary) (S T : Submodule Binary (I → Binary))
    (h : PureAnnihilates M S T) (A : Matrix P I Binary) (B : Matrix Q I Binary)
    (hA : S ≤ LinearMap.ker A.mulVecLin) (hB : T ≤ LinearMap.ker B.mulVecLin) :
    A * M * B.transpose = 0 := by
  ext p q
  let φ := (LinearMap.proj p).comp A.mulVecLin
  let ψ := (LinearMap.proj q).comp B.mulVecLin
  have hφ : S ≤ LinearMap.ker φ := by
    intro v hv; change (A.mulVecLin v) p = 0
    rw [hA hv]; rfl
  have hψ : T ≤ LinearMap.ker ψ := by
    intro v hv; change (B.mulVecLin v) q = 0
    rw [hB hv]; rfl
  have hc := annihilator_contraction M S T h φ ψ hφ hψ
  have hcoords : dualCoordinates ψ = B q := by
    ext i
    simp [dualCoordinates, ψ, Matrix.mulVec_single, Matrix.col]
  rw [hcoords] at hc
  change (A.mulVecLin (M.mulVecLin (B q))) p = 0 at hc
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
    Finset.mul_sum] at hc
  rw [Finset.sum_comm] at hc
  simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.zero_apply,
    Finset.sum_mul, mul_assoc] using hc

/--
---
conclusion: Lax342547.TensorAnnihilators.selected_block
---
The explicit affine-ray projection kills exactly the selected ray.
Pure annihilation therefore kills its tensor sandwich, and the moment
identities reduce the block to its selected point moment.
-/
theorem selected_block {Base : Type} [Fintype Base] [DecidableEq Base]
    (z : Base → Binary) (Z : Matrix (Option Base) (Option Base) Binary)
    (hZ : IsBaseMoment Z)
    (h : PureAnnihilates Z (Submodule.span Binary {baseEval z})
      (Submodule.span Binary {baseEval z})) :
    Z = Z none none • baseMoment z := by
  have hk : Submodule.span Binary {baseEval z} ≤ LinearMap.ker (rayProjection z).mulVecLin :=
    (SelectedMoments.projection_kernel z).ge
  exact SelectedMoments.moment_ray z Z hZ
    (pure_sandwich Z _ _ h (rayProjection z) (rayProjection z) hk hk)

end Lax342547Proofs.TensorAnnihilators
