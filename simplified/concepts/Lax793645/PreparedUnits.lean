import Lax793645.ConstructionData

/-!
---
title: Preparing the distribution of units
type: lemma
---
One positive quota works in all large dimensions for every admissible initial law. The
retained distribution has spreading leaves and falls into the alternative with no
common prediction or one of the compatible exact prediction cases.
-/

namespace Lax793645.PreparedUnits

section
open Lax793645.ConstructionData.Binary
open Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Filter PreparationParameters PredictionClass Function Finset
open scoped Topology BigOperators
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {M : ℕ} {q : PreparationParameters}
  {m : cycleM p} {s : OneRhythms p M} {w : OneTale p M} {l : Filter ℕ}

axiom one_finite_preparation (hq : OnePlanted q p M) :
    ∃ k,∀ᶠ n : ℕ in atTop,∀ (m : Mixer p n) (w : Wgt (OneUnit p n (M* n)))
      (s : OneLeafMixture p n (M* n)),OneNascent q m w → OneEntered q m w s →
      OnePreparedAt q m w k

end

end Lax793645.PreparedUnits
