import Lax793645Proofs.Simplifications.QuadraticPrescribedKernels
import Lax793645Proofs.Simplifications.QuadraticKernelSieve

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Function Module Submodule
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I R : Type} [Fintype I] [Fintype R] [DecidableEq I] [DecidableEq R] {N : ℕ}

def quadraticRelation (L : Mat R I) (Q : Mat R R) (z : Rack I N) : Prop:=
  (L.mulVecLin.ker ≤ z.1.mulVecLin.ker ∧L.mulVecLin.ker ≤ z.2.mulVecLin.ker) ∧
    quadraticPairCode z=quadraticGramCode (Lᵀ*Q*L)

/-- Quotient coordinates sample exactly the original-column quadratic
relation law. All nominal relations remain visible to Fourier expansion. -/
theorem quotient_quadratic_law (L : Mat R I) (hL : Surjective L.mulVec) (Q : Mat R R) :
    mapW (onW (pairW unif unif : Wgt (Rack R N))
      (fun z=>quadraticPairCode z=quadraticGramCode Q))
      (fun z=>(z.1*L,z.2*L))=unifOn (quadraticRelation L Q) := by
  let T:=(rmult (Fin N) L).prodMap (rmult (Fin N) L)
  let p (z : Rack I N):=L.mulVecLin.ker ≤ z.1.mulVecLin.ker ∧L.mulVecLin.ker ≤ z.2.mulVecLin.ker
  have hr : (fun z=>z∈LinearMap.range T)=p := by
    funext z
    apply propext
    constructor
    · rintro ⟨⟨X,Y⟩,h⟩
      rcases Prod.ext_iff.mp h with ⟨hX,hY⟩
      change X*L=z.1 at hX
      change Y*L=z.2 at hY
      constructor
      · intro v hv
        change z.1*ᵥv=0
        rw [←hX,←Matrix.mulVec_mulVec]
        rw [show L*ᵥv=0 from hv,Matrix.mulVec_zero]
      · intro v hv
        change z.2*ᵥv=0
        rw [←hY,←Matrix.mulVec_mulVec]
        rw [show L*ᵥv=0 from hv,Matrix.mulVec_zero]
    · intro hz
      obtain ⟨X,hX⟩:=factor_through_quotient L z.1 hz.1
      obtain ⟨Y,hY⟩:=factor_through_quotient L z.2 hz.2
      exact ⟨(X,Y),Prod.ext hX hY⟩
  have hμ : mapW unif T=unifOn p:=by rw [unif_lin,hr]
  have he : (fun z : Rack R N=>quadraticPairCode z=quadraticGramCode Q)=
      (fun z : Rack I N=>quadraticPairCode z=quadraticGramCode (Lᵀ*Q*L))∘T := by
    funext z
    exact propext (quadratic_pair_quotient L hL z Q).symm
  rw [←pair_unif,he]
  change mapW (onW unif (_∘T)) T=_
  rw [map_condition,hμ,unifOn_and]
  rfl

theorem quadratic_relation_law (L : Mat R I) (hL : Surjective L.mulVec) (Q : Mat R R)
    (hN : 2*num R+2 ≤ N) : IsLaw (unifOn (quadraticRelation (N:=N) L Q)) := by
  have hh:=mapW_law (on_law (pairW_law unif_law unif_law).nz (quadratic_pair_code_pos Q hN))
    (fun z : Rack R N=>(z.1*L,z.2*L))
  rwa [quotient_quadratic_law L hL Q] at hh

theorem quadratic_relation_exact_mass (L : Mat R I) (hL : Surjective L.mulVec) (Q : Mat R R)
    (hN : 2*num R+2 ≤ N) :
    (1:ℝ)/8 ≤ pr (unifOn (quadraticRelation (N:=N) L Q))
      (fun z=>(stackMatrixEquiv N z).mulVecLin.ker=L.mulVecLin.ker) := by
  rw [←quotient_quadratic_law L hL Q,mapW_pr]
  simp only [stack_matrix_quotient,exact_kernel_mul_iff L hL]
  exact quadratic_conditioned_injective_mass Q hN

theorem quotient_quadratic_exact_law (L : Mat R I) (hL : Surjective L.mulVec) (Q : Mat R R) :
    mapW (unifOn (quadraticPairGood (N:=N) Q)) (fun z=>(z.1*L,z.2*L))=
      unifOn (quadraticPrescribedKernel L Q) := by
  let T (z : Rack R N):=(z.1*L,z.2*L)
  let ok (z : Rack I N):=(stackMatrixEquiv N z).mulVecLin.ker=L.mulVecLin.ker
  have he : quadraticPairGood (N:=N) Q=
      (fun z=>quadraticPairCode z=quadraticGramCode Q ∧ok (T z)) := by
    funext z
    simp only [quadraticPairGood,ok,T,stack_matrix_quotient,exact_kernel_mul_iff L hL]
    exact propext and_comm
  rw [he,←unifOn_and]
  change mapW (onW (unifOn (fun z : Rack R N=>quadraticPairCode z=quadraticGramCode Q)) (ok∘T)) T=_
  rw [map_condition]
  have hh:=quotient_quadratic_law (N:=N) L hL Q
  rw [←pair_unif,on_unif] at hh
  rw [show mapW (unifOn (fun z : Rack R N=>quadraticPairCode z=quadraticGramCode Q)) T=
    unifOn (quadraticRelation L Q) from hh,unifOn_and]
  congr 1
  funext z
  apply propext
  constructor
  · rintro ⟨hr,hk⟩
    exact ⟨hk,hr.2⟩
  · rintro ⟨hk,hq⟩
    refine ⟨⟨?_,hq⟩,hk⟩
    have hh : L.mulVecLin.ker ≤ z.1.mulVecLin.ker⊓z.2.mulVecLin.ker:=by
      rw [←stack_matrix_kernel,hk]
    exact ⟨hh.trans inf_le_left,hh.trans inf_le_right⟩

end
end Lax793645Proofs.Simplifications
