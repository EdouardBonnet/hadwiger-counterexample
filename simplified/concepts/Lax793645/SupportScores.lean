import Lax793645.ConstructionData

/-!
---
title: Suppression of large support scores
type: lemma
---
If successful overlaps vanish, then for any positive score threshold and error
tolerance there are bounded common linear coordinates on which the probability of an
eligible generic option above threshold is small. The coordinates are chosen before
filters that can depend on both leaves.
-/

namespace Lax793645.SupportScores

section
open Lax793645.ConstructionData.Binary
open Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open PreparationParameters StatusAnalysis Filter Finset Function
open scoped Topology BigOperators
set_option backward.isDefEq.respectTransparency false
variable {p:Shape} {M s0:ℕ} {q:PreparationParameters} {l:Filter ℕ}
  {m:cycleM p} {s:OneRhythms p M} {w:OneTale p M}

axiom one_generic_lightmap (v:OneStations p M (onePreparationPins q) s)
    (h:OneVeil p M q s0 l m s w) (a ε τ:ℝ) (ha:0< a) (he:0<ε) (hτ:0<τ)
    (L R:ℕ) (Y:∀ n,OneSilhouette p (M* n) L)
    (hY:∀ n,OneFullLinearSilhouette (Y n) R):
    ∃ r coords:ℕ,∃ δ:ℝ,∀ᶠ n in l,
      ∃ X:OneSilhouette p (M* n) r,OneRefines X (Y n) ∧ OneFullLinearSilhouette X coords ∧
        OneGenericBeams (m n) X (s n) (w n) (v n) a ε δ τ

end

end Lax793645.SupportScores
