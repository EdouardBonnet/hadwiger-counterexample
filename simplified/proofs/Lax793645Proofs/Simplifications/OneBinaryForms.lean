import Lax793645Proofs.Simplifications.QuadraticCrossRanks
import Lax793645Proofs.Simplifications.OneFrameImages
import Lax793645Proofs.Simplifications.QuadraticTargetSolvability

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Module Function Finset Filter
open scoped Classical BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N : ℕ}

def onePrimalRack (P : OneFrame p n N) : Rack (Row p n) N:=onePeer 1 P
def oneDuel (P Q : OneFrame p n N) : Moment p n:=
  quadraticFrameCross (onePrimalRack P) (onePrimalRack Q)
def oneIssue (c : Vec (Comp p.g)) (x y : OneOrient p n N) : Moment p n:=
  ∑ e,c e •oneDuel (x e) (y e)

theorem one_primal_rack_frame (P : OneFrame p n N) :
    stackFrameEquiv N (onePrimalRack P)=onePrimal P := by
  unfold onePrimalRack onePeer
  rw [Equiv.apply_symm_apply]
  apply LinearMap.ext
  intro v
  simp only [LinearMap.comp_apply,Matrix.mulVecLin_apply,Matrix.one_mulVec]

theorem quadratic_frame_cross_value {I : Type} [Fintype I] [DecidableEq I]
    (P Q : Rack I N) (v w : Vec I) :
    evmat (quadraticFrameCross P Q) v w=
      (hyperbolicMatrix N).toQuadraticForm'.polarBilin
        (stackFrameEquiv N P v) (stackFrameEquiv N Q w) := by
  rw [hyperbolic_matrix_polar,hyperbolic_polar,stack_frame_apply,stack_frame_apply]
  change evmat (P.1ᵀ*Q.2+P.2ᵀ*Q.1) v w=
    dotProduct (P.1*ᵥv) (Q.2*ᵥw)+dotProduct (Q.1*ᵥw) (P.2*ᵥv)
  rw [evmat_addM]
  simp only [evmat,←Matrix.mulVec_mulVec,Matrix.dotProduct_transpose_mulVec]
  rw [dotProduct_comm (Q.2*ᵥw)]

theorem one_duel_value (P Q : OneFrame p n N) (v w : Ray p n) :
    evmat (oneDuel P Q) v w=(hyperbolicMatrix N).toQuadraticForm'.polarBilin
      (onePrimal P v) (onePrimal Q w) := by
  rw [oneDuel,quadratic_frame_cross_value,one_primal_rack_frame,one_primal_rack_frame]

theorem one_duel_same (m : Mixer p n) (o : OneOrient p n N)
    (ho : oneFrameLaw m o) (e : Comp p.g) :
    oneDuel (o e) (o e)=selfM p n m.mixM+(selfM p n m.mixM)ᵀ := by
  apply evmat_ext
  intro v w
  rw [one_duel_value]
  rw [←LinearMap.compl₁₂_apply,←QuadraticMap.polarBilin_comp]
  have he : (hyperbolicMatrix N).toQuadraticForm'.comp (onePrimal (o e))=
      (selfM p n m.mixM).toQuadraticForm' := by
    apply QuadraticMap.ext
    intro z
    exact DFunLike.congr_fun ((ho e).2.1) z
  rw [he,matrix_quadratic_polar,map_add,mpair_outer,mpair_outer,
    evmat_addM,evmat_transpose]

theorem one_duel_transpose (P Q : OneFrame p n N) : (oneDuel P Q)ᵀ=oneDuel Q P := by
  apply evmat_ext
  intro v w
  rw [evmat_transpose,one_duel_value,one_duel_value,binary_polar_symm]

theorem one_peer_primal {I : Type} [Fintype I] [DecidableEq I]
    (R : Mat (Row p n) I) (P : OneFrame p n N) :
    onePeer R P=((onePrimalRack P).1*R,(onePrimalRack P).2*R) := by
  simpa only [Matrix.one_mul,onePrimalRack] using one_peer_quotient (1 : Moment p n) R P

theorem one_duel_pull {I : Type} [Fintype I] [DecidableEq I]
    (R S : Mat (Row p n) I) (P Q : OneFrame p n N) :
    pullM R S (oneDuel P Q)=quadraticFrameCross (onePeer R P) (onePeer S Q) := by
  simp only [one_peer_primal,oneDuel,quadraticFrameCross,pullM_def,
    Matrix.mul_add,Matrix.add_mul,Matrix.transpose_mul,Matrix.mul_assoc]

/-- Each cross-endpoint polar matrix has the required binary rank with
an error exponentially small in n squared, under the actual raw law. -/
theorem one_duel_live (p : Shape) :
    ∀ᶠ n : ℕ in atTop,∀ N : ℕ,2*(n:ℝ)+2≤N→
      Fintype.card (Row p n)+2*p.h+3≤N→
      ∀ (m : Mixer p n) (R S : Mat (Row p n) (Fin n)),
      Injective R.mulVec→Injective S.mulVec→∀ W : Mat (Fin n) (Fin n),
      let μ:=quadraticChannelRaw (C:=Vec (Fin p.h))
        (hyperbolicMatrix N).toQuadraticForm' (selfM p n m.mixM).toQuadraticForm'
      pr (pairW μ μ) (fun x=>5*(pullM R S (oneDuel x.1 x.2)+W).rank<n)≤bp (-(n:ℝ)*n/20) := by
  filter_upwards [quadratic_cross_rank_calendar] with n hn N hN hroom m R S hR hS W μ
  let f:=onePeer R (N:=N)
  let g:=onePeer S (N:=N)
  have he : mapW (pairW μ μ) (Prod.map f g)=
      pairW (unifOn (quadraticPairGood (pullM R R (selfM p n m.mixM))))
        (unifOn (quadraticPairGood (pullM S S (selfM p n m.mixM)))) := by
    rw [map_pair_law,one_peer_independent m R hR hroom,one_peer_independent m S hS hroom]
  have hh:=hn N hN (pullM R R (selfM p n m.mixM)) (pullM S S (selfM p n m.mixM)) W
  rw [←he,mapW_pr] at hh
  simp only [one_duel_pull]
  convert hh using 1
  congr 1

end
end Lax793645Proofs.Simplifications
