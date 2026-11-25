import Lax793645.ConstructionData

/-!
---
title: The hole relation
type: definition
---
Two endpoints form a hole when their witnesses have the same ambient image, their
opposite functionals give the prescribed gradients, and their role bits differ.
-/

namespace Lax793645.Holes

/-- The six-term cancellation uses only these evaluations. -/
def relation {I X V : Type*} (U : I → X → V) (u : I → V → ZMod 2)
    (role : X → ZMod 2) (T : X → X → ZMod 2) (i j : I) : Prop :=
  ∃ x y : X, U i x = U j y ∧
    (∀ z, u j (U i z) = role z + T x z) ∧
    (∀ z, u i (U j z) = role z + T y z) ∧
    role x + role y = 1

/-- The relation on valid quadratic frames in the construction. -/
abbrev hole := @Lax793645.ConstructionData.Frames.oneHole

end Lax793645.Holes
