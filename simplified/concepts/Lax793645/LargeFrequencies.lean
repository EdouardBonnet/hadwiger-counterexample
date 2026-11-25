import Lax793645.ConstructionData

/-!
---
title: Large Fourier coefficients of filtered queries
type: lemma
---
A bound on the mean squared projected densities gives one bounded set containing every
frequency detected above a fixed threshold by any permitted filter on the leaf.
-/

namespace Lax793645.LargeFrequencies

section
open Lax793645.ConstructionData.Binary
open Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Finset Matrix Function
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J]

axiom filtered_large_spectrum (K : Vec I → Prop) (hK : 0 < pr unif K)
    (μ : Wgt J) (hμ : SubLaw μ) (d : J → Wgt (Vec I))
    (τ V : ℝ) (hτ : 0 < τ) (R : ℕ) (hR : V < pr unif K * (R * τ^2))
    (henergy : ∀ P : Mat (Fin R) I, densityFamilyEnergy (unifOn K) μ d P.mulVec ≤ V) :
    ∃ S : Finset (Vec I), S.card ≤ R ∧ ∀ t : Wgt J,
      (∀ j, 0 ≤ t j) → (∀ j, t j ≤ μ j) →
      ∀ ξ ∉ S, |dip (unifOn K) (mixW t d) (vectorPhase ξ)| ≤ τ

end

end Lax793645.LargeFrequencies
