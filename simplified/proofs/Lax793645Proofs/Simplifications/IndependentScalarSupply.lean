import Lax793645Proofs.Simplifications.IndependentFourEdges

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis Matrix LinearMap Submodule Module Finset Function
open IndependentClub StatusAnalysis.Guild
open scoped BigOperators
noncomputable section

theorem protected_enlarge_dim {I S : Type} [DecidableEq I] [Fintype S]
    (U : Bool → Space (Vec S)) (v : Bool → I → Vec S) (p : Finset I) (side : Bool) :
    dim (enlarge U v p side) ≤ dim (U side)+p.card := by
  classical
  have he : v side '' (p : Set I)=Set.range (fun i : p => v side i.val) := by
    ext x
    constructor
    · rintro ⟨i,hi,rfl⟩; exact ⟨⟨i,hi⟩,rfl⟩
    rintro ⟨i,rfl⟩; exact ⟨i.val,i.property,rfl⟩
  have hs : dim (Submodule.span F (v side '' (p : Set I))) ≤ p.card := by
    rw [he]
    simpa only [Set.finrank,dim,Fintype.card_coe] using
      finrank_range_le_card (R:=F) (fun i : p => v side i.val)
  exact (Submodule.finrank_add_le_finrank_add_finrank _ _).trans (Nat.add_le_add_left hs _)

variable {I : Grid → Type} [∀ i,DecidableEq (I i)] {A B : Rates} {b j : ℕ}

/-- A single finite deletion budget handles all four edges, including the
span of the selectors chosen on earlier edges. -/
theorem independent_parade_of_stability (C : Congress I A B (Label b)) (hj : 1 ≤ j)
    (U : Bool → Space (Vec (SelIdx b j))) (D : ℕ) (hU : ∀ side,dim (U side) ≤ D)
    (s : Straps (Label b)) (V : StatusSp A B)
    (hstable : ∀ i,∀ t : Straps (Label b),(∀ side,(t side).card ≤ 2^(D+34)) →
      (C i).band (s⊔t)=V i)
    (hrich : ∀ i,∀ t : Straps (Label b),(∀ side,(t side).card ≤ 2^(D+34)) →
      ∀ y,∃ x,(C i).zone (s⊔t) x ∧ view _ _ ((C i).writes x)=y)
    (target : ∀ i,Suite A B i) (htarget : ∀ i,target i∈V i) :
    ∃ g,IndependentParade C U s target g Finset.univ := by
  apply independent_full_parade C U s target
  intro P hP i
  have hdim (side) : dim (enlarge U (congressDirections C) P side) ≤ D+28 :=
    (protected_enlarge_dim U (congressDirections C) P side).trans (Nat.add_le_add (hU side) hP)
  apply seven_of_deletion_stability (C i) hj _ (D+28) hdim s (view _ _) (V i) ?_ ?_
    (ker_two _) _ (htarget i)
  · simpa only [Nat.add_assoc] using hstable i
  simpa only [Nat.add_assoc] using hrich i

/-- The original scalar stabilization argument, with a larger fixed budget,
now produces certificates whose complete selector families are independent
modulo the protected spaces. -/
theorem independent_stable_supply (C : Congress I A B (Label b)) (hj : 1 ≤ j)
    (U : Bool → Space (Vec (SelIdx b j))) (D : ℕ) (hU : ∀ side,dim (U side) ≤ D)
    (hrich : richAt C (9*2^(D+34))) :
    ∃ s : Straps (Label b),Club.sizeB s (8*2^(D+34)) ∧
      ∀ target : ∀ i,Suite A B i,(∀ i,target i∈chapter C s i) →
        ∃ g,IndependentParade C U s target g Finset.univ := by
  obtain ⟨s,hs,hstable⟩ := stable_at_budget C (2^(D+34)) hrich
  refine ⟨s,hs,fun target ht => ?_⟩
  apply independent_parade_of_stability C hj U D hU s (chapter C s) hstable ?_ target ht
  intro i t ht y
  apply hrich i (s⊔t) _ y
  intro side
  exact (Finset.card_union_le ..).trans ((Nat.add_le_add (hs side) (ht side)).trans (by omega))

end
end Lax793645Proofs.Simplifications
