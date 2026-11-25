import Lax793645Proofs.Simplifications.OneChannelLaws
import Lax793645Proofs.Simplifications.OneFrameCoordinates
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.IndependentPhaseBounds
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.AmbientBatchSlots

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Module Submodule
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

def oneDualCoordinates (N : ℕ) : Vec (HyperbolicIdx N)≃ₗ[F]Vec (Fin (2*N)) :=
  (LinearEquiv.funCongrLeft F F (Equiv.sumComm (Fin N) (Fin N))).trans
    (oneAmbientCoordinates N)

theorem one_dual_coordinates_dot (N : ℕ) (v w : Vec (HyperbolicIdx N)) :
    dotProduct (oneDualCoordinates N v) (oneAmbientCoordinates N w)=
      (hyperbolicMatrix N).toQuadraticForm'.polarBilin v w := by
  rw [hyperbolic_matrix_polar,hyperbolic_polar]
  change dotProduct ((v∘Equiv.sumComm _ _)∘_)
    (w∘_) = dotProduct (v∘Sum.inl) (w∘Sum.inr)+dotProduct (w∘Sum.inl) (v∘Sum.inr)
  rw [comp_equiv_dotProduct_comp_equiv]
  simp only [dotProduct,Fintype.sum_sum_type,Function.comp_apply,
    Equiv.sumComm_apply,Sum.swap_inl,Sum.swap_inr]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

def splitChannelMatrix {A J : Type} [Fintype A] [Fintype J] :
    Mat A (J⊕J)≃ₗ[F](Mat A J×Mat A J) where
  toFun M:=(fun a j=>M a (Sum.inl j),fun a j=>M a (Sum.inr j))
  invFun M:=Matrix.fromCols M.1 M.2
  left_inv M:=by ext a j; cases j <;> rfl
  right_inv _:=rfl
  map_add' _ _:=rfl
  map_smul' _ _:=rfl

/-- Polar channel evaluations are a bijective change of coordinates on
the entire channel pair, so their uniform law is exactly the old free law. -/
def oneChannelPairEquiv (p : Shape) (N : ℕ) : OneChannels p N≃ₗ[F]HFrame p (2*N) :=
  (((LinearEquiv.arrowCongr (LinearEquiv.refl F (Vec (HyperbolicIdx p.h)))
    (oneDualCoordinates N)).trans LinearMap.toMatrix').trans splitChannelMatrix).trans
      (LinearEquiv.prodComm F _ _)

theorem one_channel_pair_x {p : Shape} {N : ℕ} (T : OneChannels p N) (j : Fin p.h) :
    (oneChannelPairEquiv p N T).2.col j=oneDualCoordinates N (T (Pi.single (Sum.inl j) 1)) := rfl

theorem one_channel_pair_y {p : Shape} {N : ℕ} (T : OneChannels p N) (j : Fin p.h) :
    (oneChannelPairEquiv p N T).1.col j=oneDualCoordinates N (T (Pi.single (Sum.inr j) 1)) := rfl

theorem one_channel_pair_uniform (p : Shape) (N : ℕ) :
    mapW unif (oneChannelPairEquiv p N)=pairW unif unif := by
  rw [←pair_unif]
  exact unif_equiv (oneChannelPairEquiv p N).toEquiv

def onePhaseCube {p : Shape} {n N : ℕ} (o : OneOrient p n N) : HCube p (2*N) :=
  fun e=>oneChannelPairEquiv p N (oneChannels (o e))

theorem one_phase_cube_cap {p : Shape} {n N : ℕ} (m : Mixer p n)
    (hroom : Fintype.card (Row p n)+2*p.h+1≤N) (hN : 4*p.h+3≤N)
    (x : HCube p (2*N)) :
    mapW (oneRaw m N) onePhaseCube x≤oneCubePrice p*lawH p (2*N) x := by
  classical
  let E:=fun a : Comp p.g→OneChannels p N=>fun e=>oneChannelPairEquiv p N (a e)
  have hh:=mapW_cap (one_channel_cube_cap m hroom hN) E x
  rw [mapW_nested] at hh
  have he : mapW (prodW (fun _ : Comp p.g=>unif)) E=lawH p (2*N) := by
    rw [mapW_repeat]
    simp only [one_channel_pair_uniform,lawH]
  rw [he] at hh
  exact hh

end
end Lax793645Proofs.Simplifications
