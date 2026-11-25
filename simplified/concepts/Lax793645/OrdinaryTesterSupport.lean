import Lax793645.ConstructionData

/-!
---
title: Private tester support and component rank
type: lemma
---
A nonzero private tester at a tag forces its outgoing component to have positive rank.
Summing over the distinct outgoing components bounds the number of these tags by total
rank.
-/

namespace Lax793645.OrdinaryTesterSupport

section
open Lax793645.ConstructionData.Binary
open Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Matrix Finset LinearMap
open scoped BigOperators
variable {p : Shape} {n : ℕ}

axiom ordinaryBit_support (hg : 3≤ p.g) (x : Profile p n) :
    (bitSupport (ordinaryBit p n x)).card≤ totalRank x

end

end Lax793645.OrdinaryTesterSupport
