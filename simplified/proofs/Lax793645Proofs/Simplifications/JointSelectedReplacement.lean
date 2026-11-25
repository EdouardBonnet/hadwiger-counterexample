import Lax793645Proofs.Simplifications.JointChannelReplacement
import Lax793645Proofs.Simplifications.JointQuadraticObstructions

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix Submodule
noncomputable section
set_option backward.isDefEq.respectTransparency false

def channelQuadraticMatrix {D : Type} [Fintype D] [DecidableEq D] (h : ℕ) (g : Vec D→ₗ[F]Hyperbolic h) : Mat D D:=
  Classical.choose (hyperbolic_matrix_representative h g)

theorem channel_quadratic_matrix_value {D : Type} [Fintype D] [DecidableEq D]
    (h : ℕ) (g : Vec D→ₗ[F]Hyperbolic h) (v : Vec D) :
    (channelQuadraticMatrix h g).toQuadraticForm' v=hyperbolicQuadratic h (g v):=
  (Classical.choose_spec (hyperbolic_matrix_representative h g)).1 v

variable {p : Shape} {n : ℕ} {I : Bool→Type}
  [∀ i,Fintype (I i)] [∀ i,DecidableEq (I i)]

/-- Selected atoms and effective pin profiles are the only target-value
checks needed to replace an actual joint channel map. The low-rank
baseline and all kernel-row conditions are supplied internally. -/
theorem joint_selected_replacement
    (l : ∀ i,I i→Tag p.g) (s : ∀ i,I i→Label p.b) (z : ∀ i,I i→Base p.g n)
    (hz : ∀ i j,allows (l i j) (z i j))
    (U : Bool→Space (Vec (SelIdx p.b p.j))) (V : Bool→Space (Vec (AIdx p.g n)))
    (hs : ∀ i,LinearIndependent F ((U i).mkQ∘fun j=>selV p.j (s i j)))
    (ht : ∀ i,LinearIndependent F ((V i).mkQ∘fun j=>baseV (z i j)))
    (P : Bool→Comp p.g→Space (Ray p n)) (hPL : ∀ i e,P i e≤tensorCross (U i) (V i))
    (h : ℕ) (C : Comp p.g→Space (Hyperbolic h))
    (G : Comp p.g→JointRay p n→ₗ[F]Hyperbolic h)
    (hKP : ∀ e i,Disjoint (frozenChannelKernel h
      (jointSpace (fun i=>P i e⊔selectedAtComponent (l i) (s i) (z i) e)) (C e)
      ((G e).domRestrict (jointSpace (fun i=>P i e⊔selectedAtComponent (l i) (s i) (z i) e))))
      ((P i e).map (jointInjection i)))
    (R : ℕ)
    (hR : ∀ e,2*dim (jointSpace (fun i=>P i e⊔selectedAtComponent (l i) (s i) (z i) e))≤R)
    (hP : ∀ i e,∀ v∈P i e,Matrix.rank (flattenMatrix.symm v)≤R^2+Fintype.card (I i)→
      v∈tensorRectangle (U i) (V i))
    (M : JointProfile p n) (f c r : ℕ)
    (hF : ∀ e,dim (jointSpace (fun i=>P i e⊔selectedAtComponent (l i) (s i) (z i) e))≤f)
    (hC : ∀ e,dim (C e)≤c) (hM : ∀ e,(M e).rank≤r)
    (ha : ∀ i j,jointMatrixFunctional M (jointEndpointMap i (atom p (l i j) (s i j) (z i j)))=
      jointMatrixFunctional (fun e=>channelQuadraticMatrix h (G e))
        (jointEndpointMap i (atom p (l i j) (s i j) (z i j))))
    (hp : ∀ y∈jointXspace,(∀ e,y e∈quadraticSquares (jointSpace (fun i=>P i e)))→
      jointMatrixFunctional M y=jointMatrixFunctional (fun e=>channelQuadraticMatrix h (G e)) y)
    (hroom : r+(f+c)+jointCompressionRank p f (2*f+(f+c))+5*c+6*f+2≤h) :
    ∃ (Q : JointProfile p n) (g : Comp p.g→JointRay p n→ₗ[F]Hyperbolic h),
      (∀ e v,hyperbolicQuadratic h (g e v)=(Q e).toQuadraticForm' v) ∧
      (∀ e,∀ v∈jointSpace (fun i=>P i e⊔selectedAtComponent (l i) (s i) (z i) e),g e v=G e v) ∧
      (∀ e v,∀ a∈C e,(hyperbolicQuadratic h).polarBilin (g e v) a=
        (hyperbolicQuadratic h).polarBilin (G e v) a) ∧
      (∀ x∈jointXspace,jointMatrixFunctional Q x=jointMatrixFunctional M x) ∧
      ∀ e,(Q e).rank≤r+(f+c)+jointCompressionRank p f (2*f+(f+c)) := by
  apply joint_channel_replacement h
    (fun e=>jointSpace (fun i=>P i e⊔selectedAtComponent (l i) (s i) (z i) e)) C G M
    (fun e=>channelQuadraticMatrix h (G e)) (fun e v=>channel_quadratic_matrix_value h (G e) v)
    f c r hF hC hM ?_ hroom
  intro x hx hquad
  have hh:=joint_quadratic_obstruction_test l s z hz U V hs ht P _ hPL
    (fun e=>frozen_channel_kernel_le ..) hKP R hR hP
    (jointMatrixFunctional M-jointMatrixFunctional (fun e=>channelQuadraticMatrix h (G e)))
    (fun i j=>sub_eq_zero.mpr (ha i j)) (fun y hy hpy=>sub_eq_zero.mpr (hp y hy hpy)) x hx hquad
  exact sub_eq_zero.mp hh

end
end Lax793645Proofs.Simplifications
