import Lax793645.ConstructionData

/-!
---
title: Conditioning on frame images
type: lemma
---
A distribution satisfying the initial pointwise density bounds has a positive-mass
family of conditional laws. On each part, the stored directions are closed under the
endpoint and channel projections, and every further image prescription obeys the
spreading bound.
-/

namespace Lax793645.ClosedPins

section
open Lax793645.ConstructionData.Binary
open Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Filter Finset
open scoped Topology
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N : ℕ}

axiom one_first_leaves (m : Mixer p n) (w : Wgt (OneUnit p n N))
    (D ζ : ℝ) (K : ℕ) (hz : 0<ζ) (hz' : ζ<1)
    (hN : 2* dim (OneFull p n)+3≤ N)
    (hroom : (dim (OneFull p n):ℝ)+2≤((ζ/6)/4)*(2* N))
    (hcap : ∀ x,w x≤ bp (D*(2* N))* oneUnitRaw m N x) (hw : ∀ x,0≤ w x)
    (P : OneUnit p n N→ Prop) (hK : D+ζ≤((ζ/6)-(ζ/6)/4)* K) :
    ∃ s : OneLeafMixture p n N,oneLeafStrength s w m (D+K+1) ζ K ∧ s.within P ∧
      pr w P-bp (-ζ*(2* N))≤ s.amount w

end

end Lax793645.ClosedPins
