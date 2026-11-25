import Lax793645.ConstructionData

/-!
---
title: Frequencies shared by independent leaves
type: lemma
---
Each leaf carries a frequency space of dimension at most $r$. Outside pair mass
$\eta$, the intersection of two independently sampled spaces lies in one fixed space
of dimension at most $r2^r/\eta$, up to rounding.
-/

namespace Lax793645.SharedFrequencies

section
open Lax793645.ConstructionData.Binary
open Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Module Submodule Finset
set_option backward.isDefEq.respectTransparency false
axiom shared_leaf_frequencies
    {I Λ : Type} [Fintype I] [Fintype Λ] (μ : Wgt Λ) (hμ : IsLaw μ)
    (W : Λ → Space (Vec I)) (r : ℕ) (hr : ∀ l,dim (W l) ≤ r)
    (η : ℝ) (hη : 0 < η) :
    ∃ H : Space (Vec I), (dim H : ℝ) ≤ r * bp r / η ∧
      pr (pairW μ μ) (fun l => ¬ W l.1 ⊓ W l.2 ≤ H) ≤ η

end

end Lax793645.SharedFrequencies
