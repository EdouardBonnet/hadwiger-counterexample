import Lax793645Proofs.Simplifications.IndependentLabelClosures

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis Matrix LinearMap Submodule Module Finset Function
open scoped BigOperators
noncomputable section

namespace IndependentClub
variable {I X Y : Type} [DecidableEq I]
variable [AddCommGroup X] [Module F X] [Module.Finite F X]
variable [AddCommGroup Y] [Module F Y] {b j : ℕ}

/-- A robust scalar span admits a certificate of at most seven generators
with selector independence on both sides, at any positive selector degree. -/
theorem seven_of_deletion_stability (C : Club I X (Label b)) (hj : 1 ≤ j)
    (U : Bool → Space (Vec (SelIdx b j))) (D : ℕ) (hU : ∀ side,dim (U side) ≤ D)
    (s : Straps (Label b)) (π : X →ₗ[F] Y) (V : Space X)
    (hstable : ∀ t : Straps (Label b),(∀ side,(t side).card ≤ 2^(D+6)) → C.band (s⊔t)=V)
    (hrich : ∀ t : Straps (Label b),(∀ side,(t side).card ≤ 2^(D+6)) →
      ∀ y,∃ i,C.zone (s⊔t) i ∧ π (C.writes i)=y)
    (hdim : dim (V ⊓ LinearMap.ker π : Space X) ≤ 2) (x : X) (hx : x∈V) :
    ∃ p : Finset I,bundle C U (labelDirections C) p s ∧
      C.contents p=x ∧ 1 ≤ p.card ∧ p.card ≤ 7 := by
  classical
  have hsize (side) : (closure C U ∅ side).card ≤ 2^(D+6) :=
    (closure_card C hj U ∅ side).trans (Nat.pow_le_pow_right (by decide) (by
      have h := hU side
      simp only [Finset.card_empty,Nat.add_zero]
      omega))
  apply seven_list C U (labelDirections C) s π V ?_ hdim ?_ x hx
  · intro p hp
    apply ration_of_deletion_stability C hj U D 4 hU s π V _ _ p hp
    · simpa only [Nat.add_assoc] using hstable
    simpa only [Nat.add_assoc] using hrich
  intro y
  obtain ⟨i,hi,he⟩ := hrich (closure C U ∅) hsize y
  have hv : C.writes i∈V := (hstable _ hsize) ▸ C.band_write _ hi
  have hf := zone_closure_fresh C U s ∅ hi
  have hn : ∀ side,(U side).mkQ (labelDirections C side i) ≠ 0 := by
    simpa only [fresh,Finset.coe_empty,Set.image_empty,Submodule.span_empty,
      Submodule.mem_bot] using hf
  exact ⟨i,C.zone_smaller le_sup_left i hi,hv,he,hn⟩

end IndependentClub
end
end Lax793645Proofs.Simplifications
