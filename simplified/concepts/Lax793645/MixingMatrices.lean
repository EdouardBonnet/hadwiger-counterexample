import Lax793645.ConstructionData

/-!
---
title: Choosing the mixing matrices
type: lemma
---
For all sufficiently large base dimensions there is one family of matrices with the
required unary polar ranks and binary mixing ranks. The choice is uniform in the
profiles and labels tested later.
-/

namespace Lax793645.MixingMatrices

section
open Lax793645.ConstructionData.Binary
open Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Matrix Filter
open scoped BigOperators Topology Classical
set_option backward.isDefEq.respectTransparency false

axiom goodReducedMixers (p : Shape) (K s0 : ℕ) (hg : 3≤ p.g) (hodd : Odd p.g)
    (hj : 1≤ p.j) (h0 : profileA p K≤ s0) (hJ : s0≤ p.J) :
    ∀ᶠ n : ℕ in atTop,∃ m : Mixer p n,unaryGood m K s0 ∧ reducedBinaryGood m

end

end Lax793645.MixingMatrices
