import Lax793645Proofs.Simplifications.SelectedTensorSeparation

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix Submodule Module
open scoped BigOperators
noncomputable section

variable {S T I : Type} [Fintype S] [Fintype T] [Fintype I]

/-- The matrix stage of the new annihilator proof. It starts with the two
actual pin quotients, confines only the original component, and isolates the
selected atoms with a remainder in the common protected cross. -/
theorem protected_tensor_annihilator
    (U : Space (Vec S)) (V : Space (Vec T)) (P Q : Space (Vec (S × T)))
    (s : I → Vec S) (t : I → Vec T)
    (hs : LinearIndependent F (U.mkQ ∘ s)) (ht : LinearIndependent F (V.mkQ ∘ t))
    (εS : Vec S) (εT : Vec T) (hs1 : ∀ i, dotProduct εS (s i)=1)
    (ht1 : ∀ i, dotProduct εT (t i)=1) (R : ℕ)
    (hP : ∀ x ∈ P, Matrix.rank (flattenMatrix.symm x) ≤ R^2+Fintype.card I →
      x ∈ tensorRectangle U V)
    (hQ : ∀ x ∈ Q, Matrix.rank (flattenMatrix.symm x) ≤ R^2+Fintype.card I →
      x ∈ tensorRectangle U V)
    (w : Mat (S × T) (S × T)) (hw : w ∈ affineTensorSpace εS εT)
    (hR : w.rank ≤ R)
    (hv : vanish (P ⊔ selectedTensorSpace s t) (Q ⊔ selectedTensorSpace s t) w) :
    ∃ (c : I → F) (w₀ : Mat (S × T) (S × T)),
      w=(∑ i, c i • vecMulVec (tensorRay (s i) (t i)) (tensorRay (s i) (t i)))+w₀ ∧
      w₀ ∈ box (tensorCross U V) (tensorCross U V) := by
  have hids := affineTensor_identities εS εT hw
  have hsym : wᵀ=w := by
    ext x y
    exact (separate_symmetry_total w hids.selector_sym hids.base_sym y x)
  apply tensor_atom_isolation U V s t hs ht εS εT hs1 ht1 w hw
  apply protected_quotient_vanish w hsym hids.base_sym s t P Q _ _ _ hv
  · intro x hx hr
    exact hP x hx (hr.trans (Nat.add_le_add_right (Nat.pow_le_pow_left hR 2) _))
  · intro x hx hr
    exact hQ x hx (hr.trans (Nat.add_le_add_right (Nat.pow_le_pow_left hR 2) _))

end
end Lax793645Proofs.Simplifications
