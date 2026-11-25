import Lax793645.ConstructionData

/-!
---
title: From matching keys to four holes
type: lemma
---
The accepted key overlap is bounded by the probability of four cross holes times the
cost of matching the ambient columns, plus an exponentially small pruning error. The
bound applies to the two independently drawn leaves with their filters.
-/

namespace Lax793645.QueryCollision

section
open Lax793645.ConstructionData.Binary
open Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Filter Matrix
open scoped Topology

axiom one_collision_calendar (p:Shape) (K:ℕ):
    ∀ᶠ M:ℕ in atTop,∀ᶠ n:ℕ in atTop,let N:=M* n;
      100≤2* N ∧ (dim (OneCheckGram p n):ℝ)≤0.01*(2* N) ∧
      (K+(oneMaxSlots p:ℝ))* num (OneColumn p n)≤0.005*(2* N)

end

end Lax793645.QueryCollision
