import Lax793645Proofs.Simplifications.ProjectionRefinementBounds
import Mathlib.Algebra.Order.Group.MinMax

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
noncomputable section

theorem syrup_nonexpansive (B x y : ℝ) : |syrup B x-syrup B y|≤|x-y| := by
  have hh:=abs_min_sub_min_le_max (max x 0) B (max y 0) B
  rw [sub_self,abs_zero,max_eq_left (abs_nonneg (max x 0-max y 0))] at hh
  exact hh.trans (abs_max_sub_max_le_abs x y 0)

theorem clipping_lcost {A : Type} [Fintype A] (ν f g : Wgt A)
    (hν : ∀ x,0≤ν x) (B : ℝ) :
    lcost ν (fun x=>syrup B (f x)) (fun x=>syrup B (g x))≤lcost ν f g :=
  avg_mono hν (fun x=>syrup_nonexpansive B (f x) (g x))

end
end Lax793645Proofs.Simplifications
