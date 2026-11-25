import Lax793645Proofs.Simplifications.QuadraticCutChannels
import Lax793645Proofs.Simplifications.QuadraticCutAnnihilators

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix Submodule
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {p : Shape} {n : ℕ} {I : Type} [Fintype I] [DecidableEq I]

/-- End-to-end quadratic realization on one endpoint's cut-profile space:
the target is checked only on effective pin profiles and selected atoms.
The frozen channel map is allowed to be singular or zero on selected keys. -/
theorem quadratic_selected_channels
    (l : I→Tag p.g) (s : I→Label p.b) (z : I→Base p.g n)
    (hz : ∀ i,allows (l i) (z i))
    (U : Space (Vec (SelIdx p.b p.j))) (V : Space (Vec (AIdx p.g n)))
    (hs : LinearIndependent F (U.mkQ∘fun i=>selV p.j (s i)))
    (ht : LinearIndependent F (V.mkQ∘fun i=>baseV (z i)))
    (P : Comp p.g→Space (Ray p n))
    (hPL : ∀ e,P e≤tensorCross U V)
    (h : ℕ) (C : Comp p.g→Space (Hyperbolic h))
    (g₀ : ∀ e,(P e⊔selectedAtComponent l s z e : Space (Ray p n))→ₗ[F]Hyperbolic h)
    (ell : ∀ e,Ray p n→ₗ[F]C e→ₗ[F]F)
    (hKP : ∀ e,Disjoint
      (frozenChannelKernel h (P e⊔selectedAtComponent l s z e) (C e) (g₀ e)) (P e))
    (R : ℕ)
    (hR : ∀ e,2*dim (P e⊔selectedTensorSpace (fun i=>selV p.j (s i))
      (fun i=>baseV (z i)) : Space (Ray p n))≤R)
    (hP : ∀ e,∀ v∈P e,Matrix.rank (flattenMatrix.symm v)≤R^2+Fintype.card I→
      v∈tensorRectangle U V)
    (M B : Profile p n) (f c b r : ℕ)
    (hF : ∀ e,dim (P e⊔selectedAtComponent l s z e : Space (Ray p n))≤f)
    (hC : ∀ e,dim (C e)≤c) (hM : ∀ e,(M e).rank≤r) (hB : ∀ e,(B e).rank≤b)
    (hval : ∀ e,∀ v : (P e⊔selectedAtComponent l s z e : Space (Ray p n)),
      (B e).toQuadraticForm' v=hyperbolicQuadratic h (g₀ e v))
    (hcompat : ∀ e,∀ (v : (P e⊔selectedAtComponent l s z e : Space (Ray p n))) (a : C e),
      ell e v a=(hyperbolicQuadratic h).polarBilin (g₀ e v) a)
    (hrow : ∀ e,∀ (v : (P e⊔selectedAtComponent l s z e : Space (Ray p n)))
      (hv : g₀ e v∈C e) (w : Ray p n),
      (B e).toQuadraticForm'.polarBilin v w=ell e w ⟨g₀ e v,hv⟩)
    (ha : ∀ i,cutMatrixFunctional M (atom p (l i) (s i) (z i))=
      cutMatrixFunctional B (atom p (l i) (s i) (z i)))
    (hp : ∀ y∈Xspace p n,(∀ e,y e∈quadraticSquares (P e))→
      cutMatrixFunctional M y=cutMatrixFunctional B y)
    (hroom : 2*(r+b+drow p f (2*f+b))+3*c+f+2≤h) :
    ∃ (Q : Profile p n) (g : Comp p.g→Ray p n→ₗ[F]Hyperbolic h),
      (∀ e,∀ v,hyperbolicQuadratic h (g e v)=(Q e).toQuadraticForm' v) ∧
      (∀ e,∀ v : (P e⊔selectedAtComponent l s z e : Space (Ray p n)),g e v=g₀ e v) ∧
      (∀ e,∀ (v : Ray p n) (a : C e),(hyperbolicQuadratic h).polarBilin (g e v) a=ell e v a) ∧
      (∀ x∈Xspace p n,cutMatrixFunctional Q x=cutMatrixFunctional M x) ∧
      ∀ e,(Q e).rank≤r+b+drow p f (2*f+b) := by
  apply quadratic_cut_channels h (fun e=>P e⊔selectedAtComponent l s z e) C g₀ ell M B
    f c b r hF hC hM hB hval hcompat hrow ?_ hroom
  intro x hx hquad
  have hh:=quadratic_cut_obstruction_test l s z hz U V hs ht P
    (fun e=>frozenChannelKernel h (P e⊔selectedAtComponent l s z e) (C e) (g₀ e))
    hPL (fun e=>frozen_channel_kernel_le ..) hKP R hR hP
    (cutMatrixFunctional M-cutMatrixFunctional B)
    (fun i=>sub_eq_zero.mpr (ha i)) (fun y hy hpy=>sub_eq_zero.mpr (hp y hy hpy)) x hx hquad
  exact sub_eq_zero.mp hh

end
end Lax793645Proofs.Simplifications
