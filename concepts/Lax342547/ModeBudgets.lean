import Lax342547.ListDeficits

/-!
---
title: Exposed mode dimension budget
type: lemma
---
The span of any subset of rank-bounded mode spaces has dimension at most the single-space budget times the full sample size.
-/

namespace Lax342547.ModeBudgets

open scoped BigOperators

axiom mode_span_budget {K V ι : Type} [Field K] [Fintype ι] [DecidableEq ι]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (S : ι → Submodule K V) (r : ℝ) (hr : 0 ≤ r)
    (hS : ∀ i, (Module.finrank K (S i) : ℝ) ≤ r) (I : Finset ι) :
    (Module.finrank K (I.sup S : Submodule K V) : ℝ) ≤ r*Fintype.card ι

end Lax342547.ModeBudgets
