import Lax793645Proofs.Simplifications.QuadraticChannelRealization
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.ChannelFactorization

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix Submodule
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I : Type} [Fintype I] [DecidableEq I]

/-- Rank factorization in unused coordinate pairs realizes a quadratic
correction. Only ordinary matrix factorization is used. -/
theorem coordinate_quadratic_correction (h : ℕ) (M : Mat I I)
    (P : Space (Vec I)) (W : Space (Hyperbolic h))
    (hM : M∈box (annih P) (annih P))
    (hroom : M.rank+2*dim W≤h) :
    ∃ g : Vec I→ₗ[F] Hyperbolic h,
      (∀ v,hyperbolicQuadratic h (g v)=M.toQuadraticForm' v) ∧
      (∀ v∈P,g v=0) ∧
      ∀ v,∀ w∈W,(hyperbolicQuadratic h).polarBilin (g v) w=0 := by
  let S := W.map (LinearMap.snd F (Vec (Fin h)) (Vec (Fin h)))
  let T := W.map (LinearMap.fst F (Vec (Fin h)) (Vec (Fin h)))
  have hS : dim S≤dim W := Submodule.finrank_map_le _ _
  have hT : dim T≤dim W := Submodule.finrank_map_le _ _
  obtain ⟨A,hA,B,hB,hAB⟩ := pure_chan_split M S T P P hM
    (by rw [Fintype.card_fin]; omega)
  let g : Vec I→ₗ[F] Hyperbolic h := A.mulVecLin.prod B.mulVecLin
  refine ⟨g,?_,?_,?_⟩
  · intro v
    change dotProduct (A*ᵥv) (B*ᵥv)=M.toQuadraticForm' v
    rw [dotProduct_comm (A*ᵥv),←dotProduct_transpose_mulVec,Matrix.mulVec_mulVec,hAB]
    rw [←matrix_quadratic_outer,mpair_outer]
    rfl
  · intro v hv
    apply Prod.ext
    · exact (box_kill.mp hA).2 v hv
    · exact (box_kill.mp hB).2 v hv
  · intro v w hw
    rw [hyperbolic_polar]
    change dotProduct (A*ᵥv) w.2+dotProduct w.1 (B*ᵥv)=0
    have ha : A*ᵥv∈annih S := (box_mem ..).mp hA |>.1 ⟨v,rfl⟩
    have hb : B*ᵥv∈annih T := (box_mem ..).mp hB |>.1 ⟨v,rfl⟩
    have hs : w.2∈S := ⟨w,hw,rfl⟩
    have ht : w.1∈T := ⟨w,hw,rfl⟩
    rw [(annih_mem ..).mp ha _ hs,dotProduct_comm w.1,
      (annih_mem ..).mp hb _ ht,zero_add]

end
end Lax793645Proofs.Simplifications
