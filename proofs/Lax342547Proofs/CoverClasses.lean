import Lax342547.CoverClasses
import Lax342547Proofs.ModeBudgets

namespace Lax342547Proofs.CoverClasses
open Lax342547.CoverClasses

set_option backward.isDefEq.respectTransparency false

/--
---
conclusion: Lax342547.CoverClasses.finite_join_closed
---
-/
theorem finite_join_closed {K V ι : Type} [Field K] [DecidableEq ι]
    [AddCommGroup V] [Module K V] (P : Submodule K V → Prop) (hP : JoinClosed P)
    (S : ι → Submodule K V) (I : Finset ι) (hS : ∀ i ∈ I, P (S i)) : P (I.sup S) := by
  induction I using Finset.induction_on with
  | empty => simpa using hP.1
  | @insert i I hi ih =>
    rw [Finset.sup_insert]
    exact hP.2 _ _ (hS i (by simp)) (ih (fun j hj => hS j (by simp [hj])))

end Lax342547Proofs.CoverClasses
