import Lax793645Proofs.Simplifications.QuadraticMomentMaps
import Lax793645Proofs.Simplifications.QuadraticProtectedAnnihilators

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix Submodule
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I : Type} [Fintype I] [DecidableEq I]

def matrixPairing : LinearMap.BilinForm F (Mat I I) where
  toFun:=mpair
  map_add' M N:=LinearMap.ext (fun W=>mpair_add M N W)
  map_smul' c M:=LinearMap.ext (fun W=>mpair_smul c M W)

omit [DecidableEq I] in
theorem matrix_pairing_nondegenerate : (matrixPairing (I:=I)).Nondegenerate := by
  have kill (M : Mat I I) (h : ∀ W,mpair M W=0) : M=0 := by
    apply evmat_ext
    intro x y
    rw [←mpair_outer,h]
    simp [evmat]
  constructor
  · exact kill
  · intro M h
    apply kill M
    intro W
    rw [mpair_comm]
    exact h W

omit [DecidableEq I] in
theorem matrix_functional_representation (f : Mat I I→ₗ[F]F) : ∃ M,mpair M=f :=
  (matrixPairing.toDual matrix_pairing_nondegenerate).surjective f

theorem matrix_quadratic_polar (M : Mat I I) (v w : Vec I) :
    M.toQuadraticForm'.polarBilin v w=
      mpair M (vecMulVec v w+vecMulVec w v) := by
  rw [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar]
  simp only [←matrix_quadratic_outer,vecMulVec_add,add_vecMulVec,map_add]
  ring

/-- The proposed square-plus-cross space is exactly the system of frozen
quadratic values and kernel polar rows, including vectors in ker g0. -/
theorem quadratic_annihilator_values (P K : Space (Vec I)) (M : Mat I I) :
    (∀ W∈quadraticSquares P⊔quadraticCross K,mpair M W=0)↔
      (∀ v∈P,M.toQuadraticForm' v=0) ∧
        (∀ k∈K,∀ v,M.toQuadraticForm'.polarBilin k v=0) := by
  constructor
  · intro h
    constructor
    · intro v hv
      rw [←matrix_quadratic_outer]
      exact h _ ((show quadraticSquares P≤quadraticSquares P⊔quadraticCross K from le_sup_left)
        (Submodule.subset_span ⟨v,hv,rfl⟩))
    · intro k hk v
      rw [matrix_quadratic_polar]
      exact h _ ((show quadraticCross K≤quadraticSquares P⊔quadraticCross K from le_sup_right)
        (Submodule.subset_span ⟨k,hk,v,rfl⟩))
  · rintro ⟨hp,hk⟩
    have hh : quadraticSquares P⊔quadraticCross K≤(mpair M).ker := by
      apply sup_le
      · apply Submodule.span_le.mpr
        rintro W ⟨v,hv,rfl⟩
        change mpair M (vecMulVec v v)=0
        rw [matrix_quadratic_outer]
        exact hp v hv
      · apply Submodule.span_le.mpr
        rintro W ⟨k,hkv,v,rfl⟩
        change mpair M (vecMulVec k v+vecMulVec v k)=0
        rw [←matrix_quadratic_polar]
        exact hk k hkv v
    exact fun W hW=>hh hW

/-- Solve the linear target equations directly on the quotient by all
frozen values and kernel rows. This replaces the derivative linear system. -/
theorem quadratic_target_solvable (X : Space (Mat I I)) (P K : Space (Vec I))
    (G : X→ₗ[F]F)
    (hG : ∀ w : X,w.val∈quadraticSquares P⊔quadraticCross K→G w=0) :
    ∃ M : Mat I I,(∀ w : X,mpair M w.val=G w) ∧
      (∀ v∈P,M.toQuadraticForm' v=0) ∧
      ∀ k∈K,∀ v,M.toQuadraticForm'.polarBilin k v=0 := by
  let T:=quadraticSquares P⊔quadraticCross K
  let f:=T.mkQ.comp X.subtype
  have hker : f.ker≤G.ker := by
    intro w hw
    apply hG w
    exact (Submodule.Quotient.mk_eq_zero T).mp hw
  obtain ⟨L,hL⟩:=mem_range_comp hker
  obtain ⟨M,hM⟩:=matrix_functional_representation (L.comp T.mkQ)
  refine ⟨M,?_,(quadratic_annihilator_values P K M).mp ?_⟩
  · intro w
    rw [hM]
    exact LinearMap.congr_fun hL w
  · intro W hW
    rw [hM]
    change L (T.mkQ W)=0
    have hz : T.mkQ W=0:=(Submodule.Quotient.mk_eq_zero T).mpr hW
    rw [hz,map_zero]

end
end Lax793645Proofs.Simplifications
