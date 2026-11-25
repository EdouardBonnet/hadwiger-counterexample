import Lax793645Proofs.Simplifications.OneSelectedRealization
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.GradientRankBounds

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Module Submodule
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {D E : Type} [Fintype D] [Fintype E] [DecidableEq E]

theorem mpair_joint_injection (M : Mat (D×E) (D×E)) (W : Mat D D) (i : E) :
    mpair M (jointMatrixInjection i W)=mpair (jointMatrixBlock i M) W := by
  classical
  simp [mpair,jointMatrixInjection,jointMatrixBlock,Fintype.sum_prod_type,ite_and]

variable {p : Shape} {n N : ℕ}

theorem joint_diagonal_endpoint_value (M : Bool→Profile p n) (i : Bool) (z : Profile p n) :
    jointMatrixFunctional (jointCutEmbed M) (jointEndpointMap i z)=∑ e,mpair (M i e) (z e) := by
  rw [joint_matrix_functional_apply]
  apply Finset.sum_congr rfl
  intro e _
  rw [joint_endpoint_component,mpair_joint_injection]
  change mpair (jointMatrixBlock i (Matrix.blockDiagonal (fun j=>M j e))) (z e)=_
  rw [joint_matrix_block_diagonal]

/-- Assemble the bounded explicit gradients before quadratic compression.
Their component rank is at most twice the existing one-endpoint bound. -/
theorem one_gradient_targets {I : Type} [Fintype I]
    (v : Volley p n I) (w : I→Bool) (t : Tagging p I) (m : Mixer p n)
    (hg : Odd p.g) (hv : v.legal t) (hb : v.bounded w)
    (hd : ∀ i j,∑ a∈v.shoots w i j,v.diagonalAt a=1) :
    ∃ M : Bool→JointProfile p n,
      (∀ j e,(M j e).rank≤2*(15*p.r+14*p.J*Fintype.card (Comp p.g))) ∧
      ∀ i j z,jointMatrixFunctional (M j) (jointEndpointMap i z)=grad m (v.sumAt t w i j) z := by
  classical
  choose A ha hr using fun i j=>v.gradient_rep m hg hv (hb i j).2 (hd i j)
  refine ⟨fun j=>jointCutEmbed (fun i=>A i j),?_,?_⟩
  · intro j e
    apply (joint_diagonal_rank_le (fun i=>A i j e)).trans
    simpa using Finset.sum_le_sum (fun i (_ : i∈Finset.univ)=>hr i j e)
  intro i j z
  exact (joint_diagonal_endpoint_value _ i z).trans (ha i j z).symm

/-- The canonical quadratic target computed from the actual cross table
is exactly the opposite endpoint's hole functional. -/
theorem one_actual_channel_contract (x y : OneUnit p n N) (i j : Bool)
    (z : Profile p n) (hz : z∈Xspace p n) :
    jointMatrixFunctional (fun e=>channelQuadraticMatrix p.h
      (unitLeftChannels p.h (oneUnitActual x y e) j)) (jointEndpointMap i z)=
        oneFunctional (y j) (oneMomentEmbed (x i) z) := by
  symm
  apply one_unit_channel_contract x y
    (fun e=>unitPrimalTable p.h (oneUnitActual x y e))
    (fun e=>unitChannelTable p.h (oneUnitActual x y e))
    (fun j e=>unitLeftChannels p.h (oneUnitActual x y e) j)
    (fun i e=>unitRightChannels p.h (oneUnitActual x y e) i)
    (fun j e=>channelQuadraticMatrix p.h (unitLeftChannels p.h (oneUnitActual x y e) j))
    (fun e a b=>by rw [unit_table_coordinates])
    (fun j e a=>(channel_quadratic_matrix_value p.h _ a).symm) i j z hz

end
end Lax793645Proofs.Simplifications
