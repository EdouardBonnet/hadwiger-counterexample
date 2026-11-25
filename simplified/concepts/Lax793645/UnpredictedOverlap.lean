import Lax793645.ConstructionData

/-!
---
title: Overlap without common predictions
type: lemma
---
If all accepted overlaps were small, the support comparison would suppress every
option. In the branch without common predictions, soluble scalar lists on a positive
mass of pairs contradict that suppression.
-/

namespace Lax793645.UnpredictedOverlap

section
open Lax793645.ConstructionData.Binary
open Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open PreparationParameters StatusAnalysis StatusAnalysis.DualAnalysis Filter
open scoped Topology
variable {p:Shape} {M s0:ℕ} {q:PreparationParameters} {l:Filter ℕ}
  {m:cycleM p} {s:OneRhythms p M} {w:OneTale p M}

axiom one_quiet_end (v:OneStations p M (onePreparationPins q) s)
    (h:OneVeil p M q s0 l m s w) (hv:∀ᶠ n in l,(v n).bank) (hl:l.NeBot)
    (hout:oneLinearSilenceOutcome q l m w s):False

end

end Lax793645.UnpredictedOverlap
