import Lax793645Proofs.Simplifications.AffinePinProtection
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.FiniteAffineLaws

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Submodule Module Finset Function
open scoped BigOperators
noncomputable section

variable {b j : ℕ}

theorem affine_selector_injective (hj : 1 ≤ j) :
    Function.Injective (selV j : Label b → Vec (SelIdx b j)) := by
  classical
  intro s t h
  funext i
  have he := congrFun h (⟨{i},by simpa using hj⟩ : SelIdx b j)
  simpa [selV] using he

def selectorExcluded (U : Space (Vec (SelIdx b j))) : Finset (Label b) := by
  classical
  exact Finset.univ.filter (fun s => selV j s ∈ U)

theorem selector_excluded_card (hj : 1 ≤ j) (U : Space (Vec (SelIdx b j))) :
    (selectorExcluded U).card ≤ 2^(dim U) := by
  classical
  let f : selectorExcluded U → U := fun s =>
    ⟨selV j s.val,(Finset.mem_filter.mp s.property).2⟩
  have hf : Function.Injective f := by
    intro s t h
    apply Subtype.ext
    exact affine_selector_injective hj (congrArg Subtype.val h)
  have h := Fintype.card_le_of_injective f hf
  rw [Fintype.card_coe,Module.card_eq_pow_finrank (K:=F) (V:=U),
    show Fintype.card F=2 from ZMod.card 2] at h
  exact h

/-- Exclude the span of previous choices together with the protected selector
space. The exponential cost is fixed before choosing the label dimension. -/
theorem selector_span_excluded_card (hj : 1 ≤ j) (U : Space (Vec (SelIdx b j)))
    (L : Finset (Label b)) :
    (selectorExcluded (U ⊔ Submodule.span F (selV j '' (L : Set (Label b))))).card ≤
      2^(dim U+L.card) := by
  classical
  apply (selector_excluded_card hj _).trans
  apply Nat.pow_le_pow_right (by decide : 0 < (2:ℕ))
  have he : selV j '' (L : Set (Label b))=Set.range (fun s : L => selV j s.val) := by
    ext v
    constructor
    · rintro ⟨s,hs,rfl⟩; exact ⟨⟨s,hs⟩,rfl⟩
    rintro ⟨s,rfl⟩; exact ⟨s.val,s.property,rfl⟩
  have hh : dim (Submodule.span F (selV j '' (L : Set (Label b)))) ≤ L.card := by
    rw [he]
    simpa only [Set.finrank,dim,Fintype.card_coe] using
      finrank_range_le_card (R:=F) (fun s : L => selV j s.val)
  exact (Submodule.finrank_add_le_finrank_add_finrank _ _).trans (Nat.add_le_add_left hh _)

end
end Lax793645Proofs.Simplifications
