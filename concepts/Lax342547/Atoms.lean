import Lax342547.ConcreteCut
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Tactic.DeriveFintype

/-!
---
title: Point atoms and finite flavor distributions
type: lemma
---
Definition 5.4 on the concrete cut space. Each atom has a single nonzero
moment representative. Generic, shared-only, and pure flavors retain
exactly their specified coordinates, and always retain the # and Z blocks.
Their parameter law samples all retained bits independently and uniformly.
-/

namespace Lax342547.Atoms

set_option backward.isDefEq.respectTransparency false

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry
open Lax342547.CutProfiles Lax342547.ConcreteCut

noncomputable def atomRepresentation {k n b degree : ℕ} (l : Tag k)
    (s : Fin b → Binary) (z : Base k n → Binary)
    (hz : ∀ i, i ∉ allowedBase k n l → z i = 0) : Representation k n b degree := by
  classical
  refine ⟨Pi.single l (pointMoment selectorEval s z), ?_⟩
  intro t _
  by_cases ht : l = t
  · subst t
    simp only [Pi.single_eq_same]
    exact Submodule.subset_span ⟨s, z, hz, rfl⟩
  · simp [ht]

noncomputable def atom {k n b degree : ℕ} (l : Tag k) (s : Fin b → Binary) (z : Base k n → Binary)
    (hz : ∀ i, i ∉ allowedBase k n l → z i = 0) : Profile k n b degree :=
  (representationCut k n b degree).rangeRestrict (atomRepresentation l s z hz)

inductive Flavor (k : ℕ) where
  | generic
  | sharedOnly
  | pure (blocks : Finset (Tag k × Tag k))
  deriving Fintype

def retained {k n : ℕ} (l : Tag k) (f : Flavor k) : Set (Base k n)
  | Sum.inl ((d, t), _) => l ∈ interval k d ∧ match f with
      | .generic => True
      | .sharedOnly => False
      | .pure blocks => (d, t) ∈ blocks
  | Sum.inr (q, _) => match f with
      | .pure _ => q ≠ 0
      | _ => True

abbrev Parameters {k : ℕ} (n : ℕ) (l : Tag k) (f : Flavor k) :=
  {i : Base k n // i ∈ retained l f} → Binary

noncomputable instance {k n : ℕ} (l : Tag k) (f : Flavor k) :
    Fintype {i : Base k n // i ∈ retained l f} := Fintype.ofFinite _

noncomputable instance {k n : ℕ} (l : Tag k) (f : Flavor k) : Fintype (Parameters n l f) := by
  classical
  exact inferInstanceAs (Fintype ({i : Base k n // i ∈ retained l f} → Binary))

noncomputable def parameterValue {k n : ℕ} {l : Tag k} {f : Flavor k} (p : Parameters n l f)
    (i : Base k n) : Binary := by
  classical
  exact if hi : i ∈ retained l f then p ⟨i, hi⟩ else 0

noncomputable def parameterLaw {k : ℕ} (n : ℕ) (l : Tag k) (f : Flavor k) :
    PMF (Parameters n l f) := PMF.uniformOfFintype _

def testerSummary {k n b degree r : ℕ} (hr : 2 * r ≤ n)
    (s : Fin b → Binary) (z : Base k n → Binary) : Option (Tag k × Tag k) → Binary
  | none => blockTester (degree := degree) hr shared (pointMoment selectorEval s z)
  | some (d, t) => blockTester (degree := degree) hr (ordinary d t) (pointMoment selectorEval s z)

axiom atom_component {k n b degree : ℕ} (l : Tag k) (s : Fin b → Binary) (z : Base k n → Binary)
    (hz : ∀ i, i ∉ allowedBase k n l → z i = 0) (e : Component (Tag k)) :
    (atom (degree := degree) l s z hz).val e = if l ∈ e.val then pointMoment selectorEval s z else 0

axiom flavor_coordinates {k n : ℕ} (l : Tag k) (f : Flavor k) :
    retained (n := n) l f ⊆ allowedBase k n l ∧
      (∀ i : Fin n, sharp i ∈ retained l f) ∧ (∀ i : Fin n, free i ∈ retained l f)

axiom parameterLaw_product {k n : ℕ} (l : Tag k) (f : Flavor k) (p : Parameters n l f) :
    parameterLaw n l f p = ∏ i : {i : Base k n // i ∈ retained l f}, PMF.uniformOfFintype Binary (p i)

end Lax342547.Atoms
