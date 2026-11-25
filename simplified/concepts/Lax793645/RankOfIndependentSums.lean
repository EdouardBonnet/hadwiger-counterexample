import Lax793645.ConstructionData

/-!
---
title: The rank of a sum of dispersed tensors
type: lemma
---
Independent symmetric component tensors of bounded rank rarely have a sum of small
rank if every cover of the allowed dimension has small mass. The estimate selects a
subset of the sampled tensors and conditions only on the exposed ones.
-/

namespace Lax793645.RankOfIndependentSums

section
open Lax793645.ConstructionData.Binary
open Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open scoped BigOperators
open Finset
variable {A I : Type} [Fintype A] [Fintype I] [DecidableEq I]
variable {p : Shape} {N : ℕ}

axiom no_cover_rank (p : Shape) {N} (f : A→ Ambient p N) (w : Wgt A)
    (hw : IsLaw w) (m b r : ℕ) (hb : 1 ≤ b) (hr : 16* r< m)
    (hf : ∀ i,epoch p (f i)≤ r)
    (c : ℝ) (hc : 0 ≤ c)
    (he : ∀ S : Cov p N,(∀ i, cdSign p S i ≤ r*(2^m*(2* b))) →
      pr w (fun i => covered p S (f i)) ≤ c) :
    let s := 2^m*(2* b)
    pr (draws (Fin s) w) (fun x => 2* epoch p (∑ i,f (x i)) ≤ b) ≤
      ((2:ℝ)^s*(2:ℝ)^s)* c^b

end

end Lax793645.RankOfIndependentSums
