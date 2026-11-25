import Lax793645Proofs.Simplifications.JointQuadraticChannels
import Lax793645Proofs.Simplifications.JointQuadraticObstructions

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix Submodule
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {p : Shape} {n : ℕ} {I : Bool→Type}
  [∀ i,Fintype (I i)] [∀ i,DecidableEq (I i)]

/-- Realize both endpoint demands simultaneously by a single channel map.
Frozen images may be dependent, including relations between endpoints. -/
theorem joint_selected_channels
    (l : ∀ i,I i→Tag p.g) (s : ∀ i,I i→Label p.b) (z : ∀ i,I i→Base p.g n)
    (hz : ∀ i j,allows (l i j) (z i j))
    (U : Bool→Space (Vec (SelIdx p.b p.j))) (V : Bool→Space (Vec (AIdx p.g n)))
    (hs : ∀ i,LinearIndependent F ((U i).mkQ∘fun j=>selV p.j (s i j)))
    (ht : ∀ i,LinearIndependent F ((V i).mkQ∘fun j=>baseV (z i j)))
    (P : Bool→Comp p.g→Space (Ray p n))
    (hPL : ∀ i e,P i e≤tensorCross (U i) (V i))
    (h : ℕ) (C : Comp p.g→Space (Hyperbolic h))
    (g₀ : ∀ e,jointSpace (fun i=>P i e⊔selectedAtComponent (l i) (s i) (z i) e)→ₗ[F]Hyperbolic h)
    (ell : ∀ e,JointRay p n→ₗ[F]C e→ₗ[F]F)
    (hKP : ∀ e i,Disjoint (frozenChannelKernel h
      (jointSpace (fun i=>P i e⊔selectedAtComponent (l i) (s i) (z i) e)) (C e) (g₀ e))
      ((P i e).map (jointInjection i)))
    (R : ℕ)
    (hR : ∀ e,2*dim (jointSpace (fun i=>P i e⊔selectedAtComponent (l i) (s i) (z i) e))≤R)
    (hP : ∀ i e,∀ v∈P i e,Matrix.rank (flattenMatrix.symm v)≤R^2+Fintype.card (I i)→
      v∈tensorRectangle (U i) (V i))
    (M B : JointProfile p n) (f c b r : ℕ)
    (hF : ∀ e,dim (jointSpace (fun i=>P i e⊔selectedAtComponent (l i) (s i) (z i) e))≤f)
    (hC : ∀ e,dim (C e)≤c) (hM : ∀ e,(M e).rank≤r) (hB : ∀ e,(B e).rank≤b)
    (hval : ∀ e,∀ v : jointSpace (fun i=>P i e⊔selectedAtComponent (l i) (s i) (z i) e),
      (B e).toQuadraticForm' v=hyperbolicQuadratic h (g₀ e v))
    (hcompat : ∀ e,∀ (v : jointSpace (fun i=>P i e⊔selectedAtComponent (l i) (s i) (z i) e))
      (a : C e),ell e v a=(hyperbolicQuadratic h).polarBilin (g₀ e v) a)
    (hrow : ∀ e,∀ (v : jointSpace (fun i=>P i e⊔selectedAtComponent (l i) (s i) (z i) e))
      (hv : g₀ e v∈C e) (w : JointRay p n),
      (B e).toQuadraticForm'.polarBilin v w=ell e w ⟨g₀ e v,hv⟩)
    (ha : ∀ i j,jointMatrixFunctional M (jointEndpointMap i (atom p (l i j) (s i j) (z i j)))=
      jointMatrixFunctional B (jointEndpointMap i (atom p (l i j) (s i j) (z i j))))
    (hp : ∀ y∈jointXspace,(∀ e,y e∈quadraticSquares (jointSpace (fun i=>P i e)))→
      jointMatrixFunctional M y=jointMatrixFunctional B y)
    (hroom : r+b+jointCompressionRank p f (2*f+b)+5*c+6*f+2≤h) :
    ∃ (Q : JointProfile p n) (g : Comp p.g→JointRay p n→ₗ[F]Hyperbolic h),
      (∀ e,∀ v,hyperbolicQuadratic h (g e v)=(Q e).toQuadraticForm' v) ∧
      (∀ e,∀ v : jointSpace (fun i=>P i e⊔selectedAtComponent (l i) (s i) (z i) e),g e v=g₀ e v) ∧
      (∀ e,∀ (v : JointRay p n) (a : C e),(hyperbolicQuadratic h).polarBilin (g e v) a=ell e v a) ∧
      (∀ x∈jointXspace,jointMatrixFunctional Q x=jointMatrixFunctional M x) ∧
      ∀ e,(Q e).rank≤r+b+jointCompressionRank p f (2*f+b) := by
  apply joint_quadratic_channels h
    (fun e=>jointSpace (fun i=>P i e⊔selectedAtComponent (l i) (s i) (z i) e))
    C g₀ ell M B f c b r hF hC hM hB hval hcompat hrow ?_ hroom
  intro x hx hquad
  have hh:=joint_quadratic_obstruction_test l s z hz U V hs ht P
    (fun e=>frozenChannelKernel h
      (jointSpace (fun i=>P i e⊔selectedAtComponent (l i) (s i) (z i) e)) (C e) (g₀ e))
    hPL (fun e=>frozen_channel_kernel_le ..) hKP R hR hP
    (jointMatrixFunctional M-jointMatrixFunctional B)
    (fun i j=>sub_eq_zero.mpr (ha i j)) (fun y hy hpy=>sub_eq_zero.mpr (hp y hy hpy)) x hx hquad
  exact sub_eq_zero.mp hh

end
end Lax793645Proofs.Simplifications
