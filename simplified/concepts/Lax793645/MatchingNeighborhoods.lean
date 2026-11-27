import Lax793645.ConstructionData

/-!
---
title: A list meeting conflict neighborhoods
type: lemma
---
Draw entries independently from a finite list. A neighborhood of mass above
$\delta$ is missed by all $L$ draws with probability at most $e^{-L\delta}$.
Averaging over a reference law gives one list with this bound on its missed
mass. If the bound is below the mass of one point under the uniform law, the
list meets every neighborhood of mass above $\delta$.
-/

namespace Lax793645.MatchingNeighborhoods
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
variable {X I : Type*} [Fintype X] [Fintype I]

axiom hitting_list [Nonempty I] (f : I → X) (q : Wgt X) (hq : IsLaw q)
    (C : X → X → Prop) (L : ℕ) (δ : ℝ) :
    ∃ a : Fin L → I, pr q (fun x => (∀ j, ¬ C x (f (a j))) ∧
      δ < pr (mapW unif f) (C x)) ≤ Real.exp (-(L:ℝ)*δ)

axiom hitting_all_neighborhoods [Nonempty I] [Nonempty X] (f : I → X)
    (C : X → X → Prop) (L : ℕ) (δ : ℝ)
    (hsmall : Real.exp (-(L:ℝ)*δ) < (Fintype.card X : ℝ)⁻¹) :
    ∃ a : Fin L → I, ∀ x, (∀ j, ¬ C x (f (a j))) → pr (mapW unif f) (C x) ≤ δ

end Lax793645.MatchingNeighborhoods
