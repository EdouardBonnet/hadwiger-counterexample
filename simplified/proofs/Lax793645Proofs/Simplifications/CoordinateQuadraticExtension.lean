import Lax793645Proofs.Simplifications.CoordinateQuadraticBaseline
import Lax793645Proofs.Simplifications.CoordinateQuadraticCorrection

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix Submodule
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I : Type} [Fintype I] [DecidableEq I]

/-- Relative quadratic realization by linear equations and matrix
factorization. No extension of a quadratic isometry is used. -/
theorem coordinate_quadratic_extension (h : ℕ) (M : Mat I I) (P : Space (Vec I))
    (C : Space (Hyperbolic h)) (g₀ : P→ₗ[F] Hyperbolic h)
    (ell : Vec I→ₗ[F] C→ₗ[F] F)
    (hval : ∀ f : P,M.toQuadraticForm' f=hyperbolicQuadratic h (g₀ f))
    (hcompat : ∀ (f : P) (c : C),ell f c=(hyperbolicQuadratic h).polarBilin (g₀ f) c)
    (hrow : ∀ (f : P) (hf : g₀ f∈C) (v : Vec I),
      M.toQuadraticForm'.polarBilin f v=ell v ⟨g₀ f,hf⟩)
    (hroom : M.rank+5*dim C+6*dim P+2≤h) :
    ∃ g : Vec I→ₗ[F] Hyperbolic h,
      (∀ v,hyperbolicQuadratic h (g v)=M.toQuadraticForm' v) ∧
      (∀ f : P,g f=g₀ f) ∧
      ∀ (v : Vec I) (c : C),(hyperbolicQuadratic h).polarBilin (g v) c=ell v c := by
  classical
  obtain ⟨a,ha,hac,har,haRank⟩ := coordinate_quadratic_baseline M.toQuadraticForm'
    (hyperbolicQuadratic h) (hyperbolic_nondegenerate h) P C g₀ ell hval hcompat hrow
  change rk a≤dim C+2*dim P at haRank
  obtain ⟨B,hB,hBr⟩ := hyperbolic_matrix_representative h a
  let D := M+B
  have hDval (f : P) : D.toQuadraticForm' f=0 := by
    rw [matrix_quadratic_add,hval,hB,ha,char_two]
  have hDrow (f : P) (v : Vec I) : D.toQuadraticForm'.polarBilin f v=0 := by
    have hBp : B.toQuadraticForm'.polarBilin f v=
        (hyperbolicQuadratic h).polarBilin (a f) (a v) := by
      simp only [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar,hB,map_add]
    rw [matrix_polar_add,hBp,ha,
      binary_polar_symm (hyperbolicQuadratic h) (g₀ f) (a v),har,
      binary_polar_symm M.toQuadraticForm' v (f:Vec I),char_two]
  let E : Mat I I := 1+prj P
  let V := pullM E E D
  have hE (v : Vec I) (hv : v∈P) : E*ᵥv=0 := by
    rw [Matrix.add_mulVec,Matrix.one_mulVec,(prj_data P).fixes v hv,char_two]
  have hVbox : V∈box (annih P) (annih P) := by
    rw [box_kill]
    constructor
    · intro v hv
      change (Eᵀ*D*E)ᵀ*ᵥv=0
      rw [Matrix.transpose_mul,Matrix.transpose_mul,Matrix.transpose_transpose]
      simp only [←Matrix.mulVec_mulVec,hE v hv,Matrix.mulVec_zero]
    · intro v hv
      change (Eᵀ*D*E)*ᵥv=0
      simp only [←Matrix.mulVec_mulVec,hE v hv,Matrix.mulVec_zero]
  have hVval (v : Vec I) : V.toQuadraticForm' v=D.toQuadraticForm' v := by
    rw [quadratic_pull_apply]
    have hv : prj P*ᵥv∈P := (prj_data P).onto v
    change D.toQuadraticForm' ((1+prj P)*ᵥv)=D.toQuadraticForm' v
    rw [Matrix.add_mulVec,Matrix.one_mulVec,QuadraticMap.map_add D.toQuadraticForm',
      hDval ⟨_,hv⟩]
    change D.toQuadraticForm' v+0+D.toQuadraticForm'.polarBilin v (prj P*ᵥv)=_
    rw [binary_polar_symm D.toQuadraticForm' v (prj P*ᵥv),hDrow ⟨_,hv⟩ v,add_zero,add_zero]
  have hVr : V.rank≤M.rank+dim C+2*dim P :=
    (rank_lift_le _ _ _).trans ((mrk_add_le M B).trans (by
      have hb := hBr.trans haRank
      omega))
  let W : Space (Hyperbolic h) := C⊔a.range
  have hW : dim W≤2*dim C+2*dim P := by
    have hdim := Submodule.finrank_add_le_finrank_add_finrank C a.range
    change dim W≤dim C+rk a at hdim
    omega
  obtain ⟨d,hd,hdP,hdW⟩ := coordinate_quadratic_correction h V P W hVbox (by omega)
  refine ⟨a+d,?_,?_,?_⟩
  · intro v
    change hyperbolicQuadratic h (a v+d v)=M.toQuadraticForm' v
    have hw : a v∈W := Submodule.mem_sup_right ⟨v,rfl⟩
    rw [QuadraticMap.map_add (hyperbolicQuadratic h)]
    change hyperbolicQuadratic h (a v)+hyperbolicQuadratic h (d v)+
      (hyperbolicQuadratic h).polarBilin (a v) (d v)=_
    rw [binary_polar_symm (hyperbolicQuadratic h) (a v) (d v),hdW v _ hw,
      add_zero,hd,hVval,matrix_quadratic_add,hB]
    calc
      _ = M.toQuadraticForm' v+
          (hyperbolicQuadratic h (a v)+hyperbolicQuadratic h (a v)) := by abel
      _ = _ := by rw [char_two,add_zero]
  · intro f
    change a f+d f=g₀ f
    rw [ha,hdP f f.property,add_zero]
  · intro v c
    change (hyperbolicQuadratic h).polarBilin (a v+d v) c=ell v c
    rw [map_add,LinearMap.add_apply,hac,hdW v c (Submodule.mem_sup_left c.property),add_zero]

end
end Lax793645Proofs.Simplifications
