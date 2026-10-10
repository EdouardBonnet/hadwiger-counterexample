import Lax342547.ConcreteRecipes
import Lax342547Proofs.AtomProducts
import Lax342547Proofs.RecipeRows

namespace Lax342547Proofs.ConcreteRecipes

set_option backward.isDefEq.respectTransparency false

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry
open Lax342547.ConcreteCut Lax342547.CutProfiles Lax342547.WitnessAtoms
open Lax342547.ConcreteRecipes Lax342547.BinaryPrescriptions

/--
---
conclusion: Lax342547.ConcreteRecipes.prescribe
---
Choose the formal product bits from the numerical recipe alone. Every
tag has an incident component, so the indexed product theorem applies.
For any actual realization of these data, the concrete atom expansion
identifies its gradient matrix with the prescribed one. Bilinearity then
turns the matrix row sums into the gradients of both full witness sums.
-/
theorem prescribe {I J : Type} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
    {k copies : ℕ} (hk : 0 < k) (hcopies : 0 < copies)
    (data : I ⊕ J → Numerical k) (opposite p : I ⊕ J → Binary)
    (hrole₁ : (∑ i : I, (data (Sum.inl i)).role) + (∑ i : I, opposite (Sum.inl i)) = 1)
    (hrole₂ : (∑ j : J, (data (Sum.inr j)).role) + (∑ j : J, opposite (Sum.inr j)) = 1)
    (hcoupled : (∑ i : I, (p (Sum.inl i) + opposite (Sum.inl i))) =
      ∑ j : J, (p (Sum.inr j) + opposite (Sum.inr j))) :
    ∃ lbits rbits : (I ⊕ J) → (I ⊕ J) → ProductIndex k copies → Binary,
      (∀ x y t, ¬ allowedIndex (data x) (data y) t → lbits x y t = 0 ∧ rbits x y t = 0) ∧
      ∀ (n b degree r : ℕ) (hr : 2 * r ≤ n)
        (D : Testers (k := k) (b := b) (degree := degree) hr)
        (L R : Fin copies → Component (Tag k) → Component (Tag k) → Moment k n b degree)
        (atoms : I ⊕ J → PointAtom k n b degree),
        (∀ x, (atoms x).numerical hr = data x) →
        (∀ x y, x ≠ y → ∀ t, allowedIndex (data x) (data y) t →
          (L t.1 t.2.1 t.2.2).toBilin' (atoms x).vector (atoms y).vector = lbits x y t ∧
          (R t.1 t.2.1 t.2.2).toBilin' (atoms x).vector (atoms y).vector = rbits x y t) →
        RecipeGradients D L R atoms p := by
  obtain ⟨lbits, rbits, hzero, hrecipe⟩ := RecipeRows.recipe_bits
    (fun x => (data x).role) opposite p hrole₁ hrole₂ hcoupled
    (fun x y t => allowedIndex (data x) (data y) t)
    (fun x y => WitnessAtoms.allowed_index hk hcopies (data x) (data y))
    (fun x y => testerEntry (data x) (data y))
    (fun x y => WitnessAtoms.tester_properties.1 (data x) (data y))
    (fun x => WitnessAtoms.tester_properties.2 (data x))
  refine ⟨lbits, rbits, hzero, ?_⟩
  intro n b degree r hr D L R atoms hdata hbits
  have hentry := AtomProducts.gradient_of_prescriptions D L R atoms lbits rbits
    (by simpa only [hdata] using hzero) (by simpa only [hdata] using hbits)
  have he (x y : I ⊕ J) : gradient D L R (atoms x).profile (atoms y).profile =
      testerEntry (data x) (data y) + productSum lbits rbits x y + productSum lbits rbits y x := by
    simpa only [hdata] using hentry x y
  have ha (x : I ⊕ J) : D.role (atoms x).profile = (data x).role := by
    simpa only [hdata] using (WitnessAtoms.atom_testers D (atoms x)).1
  simpa only [RecipeGradients, map_sum, LinearMap.sum_apply, he, ha] using hrecipe

end Lax342547Proofs.ConcreteRecipes
