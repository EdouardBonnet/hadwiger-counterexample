import Lax793645Proofs.Simplifications.NetworkSieveLaw

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function LinearMap
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I G : Type} [Fintype I] [DecidableEq I] [Fintype G] [DecidableEq G]
  {p : Shape} {n N : ℕ}

omit [DecidableEq I] in
/-- Factor only for normalization and the image-kernel polynomial. The
observed columns and the original Gram mask are unchanged. -/
theorem nominal_network_factors (g : Route I G) (m : Mixer p n) (A : NomQuery p n g) :
    ∃ (L : ∀ i,Mat (Fin (A i).rank) (Port g i))
      (Q : ∀ i,Mat (Fin (A i).rank) (Fin (A i).rank)),
      (∀ i,Surjective (L i).mulVec) ∧
      exactNetworkPart (N:=N) g L Q=dependentGramPart g m A := by
  classical
  choose C L hC hL hCL using (fun i=>rank_product (A i))
  let Q i:=pullM (C i) (C i) (selfM p n m.mixM)
  refine ⟨L,Q,hL,?_⟩
  have hk i : LinearMap.ker (A i).mulVecLin=LinearMap.ker (L i).mulVecLin := by
    simpa only [hCL i] using left_injective_kernel (C i) (hC i) (L i)
  have hg i : (L i)ᵀ*Q i*L i=pullM (A i) (A i) (selfM p n m.mixM) := by
    dsimp only [Q]
    simp only [pullM_def]
    calc
      _=(C i*L i)ᵀ*selfM p n m.mixM*(C i*L i) := by
        simp only [Matrix.transpose_mul,Matrix.mul_assoc]
      _=_ := by simp only [hCL i]
  funext x
  simp only [exactNetworkPart,dependentGramPart,prescribedKernelGram,hk,hg]

/-- The actual raw frame law admits the quotient-normalized representation
used by the finite cross-batch Fourier estimate. -/
theorem raw_network_factored (g : Route I G) (m : Mixer p n)
    (hN : 2*num (Full p n)<N) (A : NomQuery p n g) :
    ∃ (L : ∀ i,Mat (Fin (A i).rank) (Port g i))
      (Q : ∀ i,Mat (Fin (A i).rank) (Fin (A i).rank)),
      (∀ i,Surjective (L i).mulVec) ∧
      mapW (forumLaw m N) (peekR p g A A)=unifOn (exactNetworkPart g L Q) := by
  obtain ⟨L,Q,hL,he⟩:=nominal_network_factors (N:=N) g m A
  exact ⟨L,Q,hL,he.symm ▸ law_peek_dependent g m hN A⟩

end
end Lax793645Proofs.Simplifications
