import Lax793645.ConstructionData

/-!
---
title: Available scalar generators
type: definition
---
A generator records the shared diagonal bit, the role and effective-basis data on both
sides, and two internal bits. Its certificate records surviving labels and statuses
possible on a common key cell. The scalar system takes spans of these vectors.
-/

namespace Lax793645.StatusGenerators

open Lax793645.ConstructionData.Frames Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Matrix LinearMap Submodule Finset Module Filter
open scoped BigOperators Topology

abbrev generators := @Lax793645.ConstructionData.Frames.genericStellar

end Lax793645.StatusGenerators
