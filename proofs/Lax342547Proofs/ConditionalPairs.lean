import Lax342547.ConditionalPairs
import Lax342547.RealCellLaws

namespace Lax342547Proofs.ConditionalPairs
open Lax342547.ConditionalPairs

set_option backward.isDefEq.respectTransparency false
open Lax342547.RealCellLaws Lax342547.PairRecovery Lax342547.CellAveraging Lax342547.RetainedImages

/--
---
conclusion: Lax342547.ConditionalPairs.subtype_pair_event
---
-/
theorem subtype_pair_event {ΩA ΩB : Type} [Fintype ΩA] [Fintype ΩB]
    (α : ΩA → ℝ) (β : ΩB → ℝ) (C : ΩA → Prop) (D : ΩB → Prop) (H : ΩA → ΩB → Prop) : by
    classical
    exact pairMass (subtypeWeights α C) (subtypeWeights β D) (fun a b => H a.val b.val) =
      pairEventMass (conditionalLaw α C) (conditionalLaw β D) H := by
  classical
  unfold pairMass pairEventMass
  calc
    (∑ a : {a // C a}, ∑ b : {b // D b}, if H a.val b.val then subtypeWeights α C a * subtypeWeights β D b else 0) =
        ∑ a : {a // C a}, subtypeWeights α C a *
          (∑ b : {b // D b}, subtypeWeights β D b * (if H a.val b.val then 1 else 0)) := by
      simp [Finset.mul_sum, mul_ite]
    _ = ∑ a : {a // C a}, subtypeWeights α C a *
          (∑ b, conditionalLaw β D b * (if H a.val b then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro a _
      congr 1
      exact Lax342547.RealCellLaws.subtype_integral β D (fun b => if H a.val b then 1 else 0)
    _ = ∑ a, conditionalLaw α C a *
          (∑ b, conditionalLaw β D b * (if H a b then 1 else 0)) :=
      Lax342547.RealCellLaws.subtype_integral α C (fun a => ∑ b, conditionalLaw β D b * (if H a b then 1 else 0))
    _ = _ := by simp [Finset.mul_sum, mul_ite]

end Lax342547Proofs.ConditionalPairs
