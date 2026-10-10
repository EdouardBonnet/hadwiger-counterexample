import Lax342547.RealCellLaws
import Lax342547.PairRecovery
import Lax342547.CellAveraging

/-!
---
title: Conditional pair laws on original cells
type: definition and theorem
---
The normalized subtype product event equals the product event of the ambient conditional laws, so actual retained-cell hole bounds feed the record-cell averaging theorem.
-/

namespace Lax342547.ConditionalPairs

open Lax342547.RealCellLaws Lax342547.PairRecovery Lax342547.CellAveraging Lax342547.RetainedImages

axiom subtype_pair_event {ΩA ΩB : Type} [Fintype ΩA] [Fintype ΩB]
    (α : ΩA → ℝ) (β : ΩB → ℝ) (C : ΩA → Prop) (D : ΩB → Prop) (H : ΩA → ΩB → Prop) : by
    classical
    exact pairMass (subtypeWeights α C) (subtypeWeights β D) (fun a b => H a.val b.val) =
      pairEventMass (conditionalLaw α C) (conditionalLaw β D) H

end Lax342547.ConditionalPairs
