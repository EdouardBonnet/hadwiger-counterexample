import Lax342547.AtomProducts
import Lax342547.RecipeRows

/-!
---
title: Numerical recipes prescribe the concrete gradients on witness atoms
type: definition and theorem
---
The bit prescriptions are chosen using only tags, tester summaries, and
opposite role/p bits. They work for every later choice of actual atoms and
mixers realizing that data and those distinct-atom evaluations. This is
the deterministic prescription assertion of Lemma 6.2(iii), without an
assumption of independence or occurrence of fixed-point evaluations.
-/

namespace Lax342547.ConcreteRecipes

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry
open Lax342547.ConcreteCut Lax342547.CutProfiles Lax342547.WitnessAtoms

def RecipeGradients {I J : Type} [Fintype I] [Fintype J]
    {k n b degree r copies : ℕ} {hr : 2 * r ≤ n}
    (D : Testers (k := k) (b := b) (degree := degree) hr)
    (L R : Fin copies → Component (Tag k) → Component (Tag k) → Moment k n b degree)
    (atoms : I ⊕ J → PointAtom k n b degree) (p : I ⊕ J → Binary) : Prop :=
  (∀ i : I, D.role (atoms (.inl i)).profile +
    gradient D L R (∑ t : I, (atoms (.inl t)).profile) (atoms (.inl i)).profile = 0) ∧
  (∀ j : J, D.role (atoms (.inr j)).profile +
    gradient D L R (∑ t : I, (atoms (.inl t)).profile) (atoms (.inr j)).profile = p (.inr j)) ∧
  (∀ j : J, D.role (atoms (.inr j)).profile +
    gradient D L R (∑ t : J, (atoms (.inr t)).profile) (atoms (.inr j)).profile = 0) ∧
  (∀ i : I, D.role (atoms (.inl i)).profile +
    gradient D L R (∑ t : J, (atoms (.inr t)).profile) (atoms (.inl i)).profile = p (.inl i))

axiom prescribe {I J : Type} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
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
        RecipeGradients D L R atoms p

end Lax342547.ConcreteRecipes
