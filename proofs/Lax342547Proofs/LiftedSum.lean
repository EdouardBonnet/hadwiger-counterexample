import Lax342547.LiftedSum
import Lax342547.SpanDeficits

namespace Lax342547Proofs.LiftedSum
open Lax342547.LiftedSum

set_option backward.isDefEq.respectTransparency false
open Lax342547.SpanDeficits Lax342547.BlockDeficits
open scoped BigOperators

/--
---
conclusion: Lax342547.LiftedSum.lifted_sum_apply
---
-/
theorem lifted_sum_apply {K V W ι : Type} [Field K] [Fintype ι]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (S : ι → Submodule K W) (T : ι → Submodule K V)
    (M : ∀ i, Module.Dual K (T i) →ₗ[K] S i) (f : Module.Dual K V) :
    liftedSum S T M f = ∑ i, (M i ((T i).subtype.dualMap f)).val := by
  classical
  simp only [liftedSum,LinearMap.comp_apply,addition,LinearMap.lsum_apply,
    LinearMap.sum_apply,LinearMap.proj_apply,Submodule.subtype_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply congrArg (fun g : Module.Dual K (T i) => (M i g).val)
  ext v
  change f ((addition T) (Pi.single i v)) = f v.val
  rw [Lax342547.SpanDeficits.addition_single]

end Lax342547Proofs.LiftedSum
