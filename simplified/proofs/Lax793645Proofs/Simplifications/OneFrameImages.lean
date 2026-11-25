import Lax793645Proofs.Simplifications.OneFrameLaws
import Lax793645Proofs.Simplifications.QuadraticRelationLaws
import Lax793645Proofs.Simplifications.QuadraticImageCaps
import Lax793645Proofs.Simplifications.DependentFrameImages

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Function
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I : Type} [Fintype I] [DecidableEq I] {p : Shape} {n N : ℕ}

/-- Two coordinate halves of a single physical image. There is only one
primal frame; the halves are not independently prescribed embeddings. -/
def onePeer (A : Mat (Row p n) I) (P : OneFrame p n N) : Rack I N:=
  (stackFrameEquiv N).symm ((onePrimal P).comp A.mulVecLin)

theorem one_peer_independent (m : Mixer p n) (A : Mat (Row p n) I)
    (hA : Injective A.mulVec)
    (hN : Fintype.card (Row p n)+2*p.h+3 ≤ N) :
    mapW (quadraticChannelRaw (C:=Vec (Fin p.h))
      (hyperbolicMatrix N).toQuadraticForm' (selfM p n m.mixM).toQuadraticForm') (onePeer A)=
      unifOn (quadraticPairGood (pullM A A (selfM p n m.mixM))) := by
  classical
  letI : Fintype (Vec I →ₗ[F] Vec (HyperbolicIdx N)):=
    Fintype.ofInjective (fun f=>⇑f) DFunLike.coe_injective
  have hd : Fintype.card I ≤ Fintype.card (Row p n):=
    (mrk_inj.mp hA).symm.le.trans A.rank_le_card_height
  have hr : Module.finrank F (Vec I)+3 ≤ N:=by
    simpa only [dim_vec] using (show Fintype.card I+3 ≤ N by omega)
  have ho:=one_frame_primal_observe m A.mulVecLin hA (by omega) hr
  rw [matrix_quadratic_comp] at ho
  have hm : LinearMap.toMatrix' A.mulVecLin=A:=Matrix.toLin'.symm_apply_apply A
  rw [hm] at ho
  change mapW _ ((stackFrameEquiv N).symm∘(fun P : OneFrame p n N=>(onePrimal P).comp A.mulVecLin))=_
  rw [←mapW_nested,ho]
  let E:=stackFrameEquiv (I:=I) N
  have hp : quadraticGramGood (hyperbolicMatrix N).toQuadraticForm'
      (pullM A A (selfM p n m.mixM)).toQuadraticForm'=
      (quadraticPairGood (pullM A A (selfM p n m.mixM)))∘E.symm := by
    funext x
    rw [Function.comp_apply,quadratic_pair_good_frame,E.apply_symm_apply]
  rw [hp]
  exact on_equiv E.symm (quadraticPairGood (pullM A A (selfM p n m.mixM)))

theorem one_peer_quotient {R : Type} [Fintype R] [DecidableEq R]
    (C : Mat (Row p n) R) (L : Mat R I) (P : OneFrame p n N) :
    onePeer (C*L) P=((onePeer C P).1*L,(onePeer C P).2*L) := by
  apply (stackFrameEquiv N).injective
  rw [show (stackFrameEquiv N) (onePeer (C*L) P)=(onePrimal P).comp (C*L).mulVecLin from
    (stackFrameEquiv N).apply_symm_apply _]
  apply LinearMap.ext
  intro v
  change onePrimal P ((C*L)*ᵥv)=stackMatrixEquiv N ((onePeer C P).1*L,(onePeer C P).2*L)*ᵥv
  rw [stack_matrix_quotient,←Matrix.mulVec_mulVec,←Matrix.mulVec_mulVec]
  exact (LinearMap.congr_fun ((stackFrameEquiv N).apply_symm_apply
    ((onePrimal P).comp C.mulVecLin)) (L*ᵥv)).symm

/-- Exact dependent observation under the actual one-frame raw law. The
only Gram constraints are quadratic ones, including physical injectivity. -/
theorem one_peer_dependent (m : Mixer p n) (A : Mat (Row p n) I)
    (hN : Fintype.card (Row p n)+2*p.h+3 ≤ N) :
    mapW (quadraticChannelRaw (C:=Vec (Fin p.h))
      (hyperbolicMatrix N).toQuadraticForm' (selfM p n m.mixM).toQuadraticForm') (onePeer A)=
      unifOn (fun z : Rack I N=>(stackMatrixEquiv N z).mulVecLin.ker=A.mulVecLin.ker ∧
        quadraticPairCode z=quadraticGramCode (pullM A A (selfM p n m.mixM))) := by
  classical
  obtain ⟨C,L,hC,hL,hCL⟩:=rank_product A
  let T (z : Rack (Fin A.rank) N):=(z.1*L,z.2*L)
  have he : onePeer A=T∘onePeer C := by
    funext x
    simpa only [hCL,T,Function.comp_apply] using one_peer_quotient C L x
  rw [he,←mapW_nested,one_peer_independent m C hC hN,quotient_quadratic_exact_law L hL]
  have hk : A.mulVecLin.ker=L.mulVecLin.ker := by
    simpa only [hCL] using left_injective_kernel C hC L
  have hg : Lᵀ*pullM C C (selfM p n m.mixM)*L=pullM A A (selfM p n m.mixM) := by
    simp only [pullM_def]
    calc
      _=(C*L)ᵀ*selfM p n m.mixM*(C*L) := by simp only [Matrix.transpose_mul,Matrix.mul_assoc]
      _=_ := by simp only [hCL]
  congr 1
  funext z
  simp only [quadraticPrescribedKernel,hk,hg]

end
end Lax793645Proofs.Simplifications
