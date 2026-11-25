import Lax793645Proofs.Simplifications.IndependentSevenLists

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis Matrix LinearMap Submodule Module Finset Function
open scoped BigOperators
noncomputable section

namespace IndependentClub
variable {I X Y : Type} [DecidableEq I]
variable [AddCommGroup X] [Module F X] [AddCommGroup Y] [Module F Y]
variable {b j : ℕ} (C : Club I X (Label b))

def labelDirections (side : Bool) (i : I) := selV j (C.addr i side)
def blocked (U : Bool → Space (Vec (SelIdx b j))) : Straps (Label b) :=
  fun side => selectorExcluded (U side)
def closure (U : Bool → Space (Vec (SelIdx b j))) (p : Finset I) : Straps (Label b) :=
  blocked (enlarge U (labelDirections (j:=j) C) p)

theorem closure_card (hj : 1 ≤ j) (U : Bool → Space (Vec (SelIdx b j)))
    (p : Finset I) (side : Bool) :
    (closure C U p side).card ≤ 2^(dim (U side)+p.card) := by
  classical
  let A := p.image (fun i => C.addr i side)
  have he : labelDirections (j:=j) C side '' (p : Set I)=selV j '' (A : Set (Label b)) := by
    ext x
    constructor
    · rintro ⟨i,hi,rfl⟩
      exact ⟨C.addr i side,Finset.mem_image.mpr ⟨i,hi,rfl⟩,rfl⟩
    rintro ⟨s,hs,rfl⟩
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hs
    exact ⟨i,hi,rfl⟩
  unfold closure blocked enlarge
  rw [he]
  exact (selector_span_excluded_card hj (U side) A).trans
    (Nat.pow_le_pow_right (by decide) (Nat.add_le_add_left Finset.card_image_le _))

theorem closure_mono (U : Bool → Space (Vec (SelIdx b j)))
    {p q : Finset I} (hp : p ⊆ q) : closure C U p ≤ closure C U q := by
  classical
  intro side s hs
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_⟩
  apply (sup_le_sup_left (Submodule.span_mono (Set.image_mono hp)) (U side))
  exact (Finset.mem_filter.mp hs).2

theorem zone_closure_fresh (U : Bool → Space (Vec (SelIdx b j)))
    (s : Straps (Label b)) (p : Finset I) {i : I}
    (hi : C.zone (s ⊔ closure C U p) i) : fresh U (labelDirections C) p i := by
  classical
  intro side hs
  apply hi.2 side
  apply Finset.mem_union_right
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_⟩
  apply quotient_span_preimage (U side) _ _
  simpa only [Set.image_image,Function.comp_def,labelDirections] using hs

theorem bundle_blocked (U : Bool → Space (Vec (SelIdx b j)))
    (s : Straps (Label b)) (p : Finset I) :
    bundle C U (labelDirections C) p (s ⊔ blocked U) ↔
      bundle C U (labelDirections C) p s := by
  classical
  constructor
  · intro h
    exact ⟨fun i hi => C.zone_smaller le_sup_left i (h.1 i hi),h.2⟩
  intro h
  refine ⟨fun i hi => ?_,h.2⟩
  refine ⟨(h.1 i hi).1,fun side hs => ?_⟩
  rcases Finset.mem_union.mp hs with hs|hs
  · exact (h.1 i hi).2 side hs
  have hn := (h.2 side).ne_zero hi
  apply hn
  exact (Submodule.Quotient.mk_eq_zero _).mpr (Finset.mem_filter.mp hs).2

theorem ration_blocked (U : Bool → Space (Vec (SelIdx b j)))
    (s : Straps (Label b)) (π : X →ₗ[F] Y) :
    ration C U (labelDirections C) (s ⊔ blocked U) π=
      ration C U (labelDirections C) s π := by
  apply congrArg (Submodule.span F)
  ext x
  change length3 C U (labelDirections C) (s ⊔ blocked U) π x ↔
    length3 C U (labelDirections C) s π x
  simp only [length3,bundle_blocked]

/-- Bounded deletion stability supplies the stronger span-stability premise
used by the independent seven-generator theorem. -/
theorem ration_of_deletion_stability (hj : 1 ≤ j)
    (U : Bool → Space (Vec (SelIdx b j))) (D r : ℕ)
    (hU : ∀ side,dim (U side) ≤ D) (s : Straps (Label b)) (π : X →ₗ[F] Y) (V : Space X)
    (hstable : ∀ t : Straps (Label b),(∀ side,(t side).card ≤ 2^(D+r+2)) →
      C.band (s⊔t)=V)
    (hrich : ∀ t : Straps (Label b),(∀ side,(t side).card ≤ 2^(D+r+2)) →
      ∀ y,∃ i,C.zone (s⊔t) i ∧ π (C.writes i)=y)
    (p : Finset I) (hp : p.card ≤ r) :
    ration C (enlarge U (labelDirections C) p) (labelDirections C) s π=V⊓LinearMap.ker π := by
  classical
  let U' := enlarge U (labelDirections (j:=j) C) p
  let s' := s ⊔ blocked U'
  have hsize (q : Finset I) (hq : q.card ≤ 2) (side) :
      (closure C U (p∪q) side).card ≤ 2^(D+r+2) :=
    (closure_card C hj U (p∪q) side).trans
      (Nat.pow_le_pow_right (by decide) (by have hc := Finset.card_union_le p q; have := hU side; omega))
  have hb : C.band s'=V := by
    apply hstable
    intro side
    have h := hsize ∅ (by simp) side
    simpa only [Finset.union_empty,closure,U'] using h
  have hn (i : I) (hi : C.zone s' i) (side) : (U' side).mkQ (labelDirections C side i) ≠ 0 := by
    intro hz
    apply hi.2 side
    apply Finset.mem_union_right
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _,(Submodule.Quotient.mk_eq_zero _).mp hz⟩
  have hy : yieldFresh C U' (labelDirections C) s' π := by
    intro q hq y
    obtain ⟨i,hi,he⟩ := hrich (closure C U (p∪q)) (hsize q hq) y
    have hc : closure C U p ≤ closure C U (p∪q) := closure_mono C U Finset.subset_union_left
    have hi' : C.zone (s ⊔ closure C U p) i :=
      C.zone_smaller (sup_le_sup_left hc s) i hi
    refine ⟨i,hi',he,?_⟩
    apply zone_closure_fresh C U' s q
    have heq : closure C U' q=closure C U (p∪q) := by
      unfold closure U'
      rw [enlarge_union]
    rwa [heq]
  rw [←ration_blocked C U' s π]
  exact (ration_eq C U' (labelDirections C) s' π hn hy).trans (by rw [hb])

end IndependentClub
end
end Lax793645Proofs.Simplifications
