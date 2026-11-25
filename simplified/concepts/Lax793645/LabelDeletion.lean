import Lax793645.ConstructionData

/-!
---
title: Deleting labels preserves the edge span
type: lemma
---
At good orientations, vanishing on generators for every surviving label gives a
quadratic identity. Continuation in the selector bits extends it to all labels, so the
resulting edge span equals the original span.
-/

namespace Lax793645.LabelDeletion

section
open Lax793645.ConstructionData.Binary
open Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open StatusAnalysis StatusAnalysis.DualAnalysis Club Guild Function LinearMap Finset Matrix Submodule
open scoped BigOperators Classical
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N r K c R : ℕ} {d e : Rates}
variable {u : Terrain p r} {s : Gazette p r d} {t : Gazette p r e}
variable {β δ η : ℝ}

axiom generic_status_band_stable (hu : origami p r u δ)
    (hs : reports p r u s β δ) (ht : reports p r u t β δ)
    (hgap : HasStatusSupportGap u s t η) (hη : 0<η) (hg : 3≤ p.g)
    (B : ℕ) (hB : B< Fintype.card (Label p.b))
    (hleft : GenericStatusContinuation u s B) (hright : GenericStatusContinuation u t B)
    (S : Straps (Label p.b)) (hS : ∀ side,(S side).card≤ B) (i : Grid) :
    (genericStellar u s t η ⊥ ⊥ i).band S=(stellar u s t η ⊥ ⊥ i).band ⊥

end

end Lax793645.LabelDeletion
