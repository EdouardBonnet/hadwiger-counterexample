import Lax793645Proofs.Simplifications.QuadraticRankReduction
import Lax793645Proofs.Simplifications.QuadraticImageCaps
import Lax793645Proofs.Simplifications.RelativeQuadraticBaseline

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix Submodule
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {I : Type} [Fintype I] [DecidableEq I]

/-- Matrix rank controls polar rank, without dividing by two in the
binary field. The ordered representative still carries the diagonal. -/
theorem matrix_quadratic_polar_rank (M : Mat I I) :
    rk M.toQuadraticForm'.polarBilin≤2*M.rank := by
  have he : M.toQuadraticForm'.polarBilin=
      (dotProductBilin F F).comp (M+Mᵀ).mulVecLin := by
    apply LinearMap.ext
    intro v
    apply LinearMap.ext
    intro w
    change M.toQuadraticForm'.polarBilin v w=dotProduct ((M+Mᵀ)*ᵥv) w
    simp only [matrix_quadratic_polar,map_add,mpair_outer,Matrix.add_mulVec,add_dotProduct]
    change evmat M v w+evmat M w v=
      dotProduct (M*ᵥv) w+dotProduct (Mᵀ*ᵥv) w
    rw [dotProduct_comm (M*ᵥv) w,dotProduct_comm (Mᵀ*ᵥv) w]
    change evmat M v w+evmat M w v=evmat M w v+evmat Mᵀ w v
    rw [evmat_transpose]
    exact add_comm _ _
  rw [he]
  exact (rk_comp_le_right _ _).trans (by
    change (M+Mᵀ).rank≤2*M.rank
    exact (mrk_add_le ..).trans_eq (by rw [Matrix.rank_transpose,two_mul]))

/-- A hyperbolic channel map of small image has an ordered quadratic
matrix representative of at most the same rank. -/
theorem hyperbolic_matrix_representative (h : ℕ) (g : Vec I→ₗ[F]Hyperbolic h) :
    ∃ M : Mat I I,(∀ v,M.toQuadraticForm' v=hyperbolicQuadratic h (g v)) ∧
      M.rank≤rk g := by
  let L:=(hyperbolicCoordinates h).symm.toLinearMap.comp g
  let A:=LinearMap.toMatrix' L
  refine ⟨pullM A A (hyperbolicMatrix h),?_,?_⟩
  · intro v
    rw [←matrix_quadratic_comp,QuadraticMap.comp_apply,hyperbolic_matrix_apply]
    exact congrArg (hyperbolicQuadratic h) ((hyperbolicCoordinates h).apply_symm_apply (g v))
  · rw [pullM_def]
    exact (Matrix.rank_mul_le_right ..).trans (by
      change A.rank≤rk g
      rw [rank_cast,toMat_map]
      exact rk_comp_le_right g (hyperbolicCoordinates h).symm.toLinearMap)

/-- Frozen values and channel projections have a baseline whose matrix
rank is bounded by their dimensions, including noninjective frozen maps. -/
theorem quadratic_matrix_baseline (h : ℕ) (P : Space (Vec I))
    (C : Space (Hyperbolic h)) (g₀ : P→ₗ[F]Hyperbolic h)
    (ell : Vec I→ₗ[F]C→ₗ[F]F)
    (hcompat : ∀ (f : P) (c : C),ell f c=(hyperbolicQuadratic h).polarBilin (g₀ f) c) :
    ∃ M : Mat I I,M.rank≤dim P+dim C ∧
      (∀ f : P,M.toQuadraticForm' f=hyperbolicQuadratic h (g₀ f)) ∧
      ∀ (f : P) (hf : g₀ f∈C) (v : Vec I),
        M.toQuadraticForm'.polarBilin f v=ell v ⟨g₀ f,hf⟩ := by
  obtain ⟨g,hg,hproj,hr⟩:=relative_quadratic_baseline (hyperbolicQuadratic h)
    (hyperbolic_nondegenerate h) P C g₀ ell hcompat
  obtain ⟨M,hM,hmr⟩:=hyperbolic_matrix_representative h g
  refine ⟨M,hmr.trans hr,?_,?_⟩
  · intro f
    rw [hM,hg]
  · intro f hf v
    have he : M.toQuadraticForm'.polarBilin f v=
        (hyperbolicQuadratic h).polarBilin (g f) (g v) := by
      simp only [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar,hM,map_add]
    rw [he,hg,binary_polar_symm]
    exact hproj v ⟨g₀ f,hf⟩

/-- The final channel step needs only an ordered bounded-rank quadratic
matrix and the frozen kernel-row conditions. -/
theorem quadratic_matrix_realize (h : ℕ) (M : Mat I I) (P : Space (Vec I))
    (C : Space (Hyperbolic h)) (g₀ : P→ₗ[F]Hyperbolic h)
    (ell : Vec I→ₗ[F]C→ₗ[F]F)
    (hval : ∀ f : P,M.toQuadraticForm' f=hyperbolicQuadratic h (g₀ f))
    (hcompat : ∀ (f : P) (c : C),ell f c=(hyperbolicQuadratic h).polarBilin (g₀ f) c)
    (hrow : ∀ (f : P) (hf : g₀ f∈C) (v : Vec I),
      M.toQuadraticForm'.polarBilin f v=ell v ⟨g₀ f,hf⟩)
    (hroom : 2*M.rank+3*dim C+dim P+2≤h) :
    ∃ g : Vec I→ₗ[F]Hyperbolic h,
      (∀ v,hyperbolicQuadratic h (g v)=M.toQuadraticForm' v) ∧
      (∀ f : P,g f=g₀ f) ∧
      ∀ (v : Vec I) (c : C),(hyperbolicQuadratic h).polarBilin (g v) c=ell v c := by
  apply hyperbolic_relative_extension h M.toQuadraticForm' P C g₀ ell hval hcompat hrow
  exact (Nat.add_le_add_right (Nat.add_le_add_right
    (Nat.add_le_add_right (matrix_quadratic_polar_rank M) _) _) _).trans hroom

end
end Lax793645Proofs.Simplifications
