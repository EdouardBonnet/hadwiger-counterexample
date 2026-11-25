import Lax793645.ConstructionData

/-!
---
title: Four holes between two random units
type: theorem
---
Fix the construction parameters and suitable mixers. In every sufficiently large
dimension, two independent draws from any admissible unit law have all four cross
holes with probability at least $2^{-200N}$, where $N$ is the full ambient dimension.
The endpoints within each unit may be dependent.
-/

namespace Lax793645.FourHoles

section
open Lax793645.ConstructionData.Binary
open Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Lax793645.ConstructionData.Binary Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Matrix Filter Finset PreparationParameters
open scoped BigOperators Topology
open Lax793645.ConstructionData.Frames.OneConstruction
set_option backward.isDefEq.respectTransparency false
variable {p:Shape} {n N M s0:ℕ} {b:PreparationParameters}

axiom eventual_conflict_lower_bound (h:OneParameters.Complete p M b s0):
    ∀ᶠ n:ℕ in atTop,∀ m:Mixer p n,unaryGood m (onePreparationPins b) s0 →
      reducedBinaryGood m → conflictLowerBound m (M* n) b

end

end Lax793645.FourHoles
