import Lax793645.ConstructionData

/-!
---
title: Safety on a rare compatible pair
type: lemma
---
For compatibility determined by a bounded family of accepting sets, the probability of
a compatible pair failing a pin test is bounded relative to the compatibility mass, up
to an exponentially small error.
-/

namespace Lax793645.SafeCompatiblePairs

section
open Lax793645.ConstructionData.Binary
open Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open PreparationParameters PredictionClass Filter Finset
open scoped BigOperators Topology
open Lax793645.ConstructionData.Frames.OneDurable
set_option backward.isDefEq.respectTransparency false
variable {l : Filter ℕ} {p : Shape} {M n N : ℕ} {q : PreparationParameters}
  {m : cycleM p} {s : OneRhythms p M} {w : OneTale p M}
variable {b : OneSketch p M}

axiom coded_safety (h : OneDurable q l m w s) (hl : l≤ atTop) (hq : OnePlanted q p M)
    (hw : ∀ᶠ n in l,OneNascent q (m n) (w n))
    (hd : ∀ᶠ n in l,oneCodedLeaves q (s n) (oneMatchProg b n)) :
    ∀ᶠ n in l,oneGleam s w b n≤0.0005* oneGlow s w b n+edgeError (2*(M* n))

end

end Lax793645.SafeCompatiblePairs
