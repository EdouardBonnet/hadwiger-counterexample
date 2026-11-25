import Lax793645Proofs.Simplifications.OneQueryImages
import Lax793645Proofs.Simplifications.QuadraticNetworkSieve

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix Function LinearMap
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I G : Type} [Fintype I] [DecidableEq I] [Fintype G] [DecidableEq G]
  {p : Shape} {n N : ℕ}

theorem one_nominal_factors (g : Route I G) (m : Mixer p n) (A : NomQuery p n g) :
    ∃ (L : ∀ i,Mat (Fin (A i).rank) (Port g i))
      (Q : ∀ i,Mat (Fin (A i).rank) (Fin (A i).rank)),
      (∀ i,Surjective (L i).mulVec) ∧
      quadraticExactNetwork (N:=N) g L Q=oneDependentGram g m A := by
  classical
  choose C L hC hL hCL using (fun i=>rank_product (A i))
  let Q i:=pullM (C i) (C i) (selfM p n m.mixM)
  refine ⟨L,Q,hL,?_⟩
  have hk i : (A i).mulVecLin.ker=(L i).mulVecLin.ker := by
    simpa only [hCL i] using left_injective_kernel (C i) (hC i) (L i)
  have hg i : (L i)ᵀ*Q i*L i=pullM (A i) (A i) (selfM p n m.mixM) := by
    dsimp only [Q]
    simp only [pullM_def]
    calc
      _=(C i*L i)ᵀ*selfM p n m.mixM*(C i*L i) := by
        simp only [Matrix.transpose_mul,Matrix.mul_assoc]
      _=_ := by simp only [hCL i]
  funext x
  simp only [quadraticExactNetwork,oneDependentGram,quadraticPrescribedKernel,hk,hg]

theorem one_raw_network_factored (g : Route I G) (m : Mixer p n)
    (hN : Fintype.card (Row p n)+2*p.h+3 ≤ N) (A : NomQuery p n g) :
    ∃ (L : ∀ i,Mat (Fin (A i).rank) (Port g i))
      (Q : ∀ i,Mat (Fin (A i).rank) (Fin (A i).rank)),
      (∀ i,Surjective (L i).mulVec) ∧
      mapW (oneForumLaw m N) (onePeek g A)=unifOn (quadraticExactNetwork g L Q) := by
  obtain ⟨L,Q,hL,he⟩:=one_nominal_factors (N:=N) g m A
  exact ⟨L,Q,hL,he.symm ▸ one_law_peek g m hN A⟩

end
end Lax793645Proofs.Simplifications
