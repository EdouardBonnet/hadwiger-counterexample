import Lax793645Proofs.Simplifications.AffineOptionRealization
import Lax793645Proofs.Simplifications.IndependentSelectorChoice

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis Matrix Submodule Module Finset Function
noncomputable section

/-- Fresh labels on a predicted branch can also be chosen independently
modulo the protected selector space. The number of positions is at most 12. -/
theorem affine_predicted_labels {p : Shape} {q : Format} {n K budget : ℕ}
    {plan : Plan p n} (H : PlanProtection plan (affineQorth K) K)
    (hj : 1 ≤ p.j) (L : Stalls p) (hL : ∀ i,(L i).card ≤ budget)
    (hs : Fintype.card (Messenger q) ≤ 12) (side : Bool)
    (hlabels : budget+2^(selectorProtectionDim p (affineQorth K) K+12) <
      Fintype.card (Label p.b)) :
    ∃ f : Messenger q → Label p.b,Injective f ∧
      (∀ i,f i ∉ L (parcel side i)) ∧
      LinearIndependent F (H.selector.mkQ ∘ fun i => selV p.j (f i)) := by
  classical
  let S (i : Messenger q) := (L (parcel side i))ᶜ
  have hpow : 2^(dim H.selector+Fintype.card (Messenger q)) ≤
      2^(selectorProtectionDim p (affineQorth K) K+12) :=
    Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) (Nat.add_le_add H.selector_dim hs)
  have hS (i : Messenger q) : 2^(dim H.selector+Fintype.card (Messenger q)) < (S i).card := by
    have hLi := hL (parcel side i)
    unfold S
    rw [Finset.card_compl]
    omega
  obtain ⟨f,hf,hLI⟩ := independent_selector_choice hj H.selector S hS
  refine ⟨f,?_,fun i => Finset.mem_compl.mp (hf i),hLI⟩
  intro i j hij
  apply hLI.injective
  change H.selector.mkQ (selV p.j (f i))=H.selector.mkQ (selV p.j (f j))
  rw [hij]

end
end Lax793645Proofs.Simplifications
