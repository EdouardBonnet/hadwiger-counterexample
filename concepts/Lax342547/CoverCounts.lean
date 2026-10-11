import Lax342547.SmallExposure

/-!
---
title: Count tensors killed by exposure
type: lemma
---
A low sum rank and a small combined mode deficit force at least the prescribed number of covered tensors among the remaining indices.
-/

namespace Lax342547.CoverCounts



axiom covered_count_lower_bound {ι : Type} (I : Finset ι) (P : ι → Prop)
    (b t : ℕ) (rank d : ℝ) (hI : I.card = b) (hbt : 2*t ≤ b)
    (hr : rank < (t : ℝ)/4) (hd : d < (b : ℝ)/4)
    (hc : by classical exact ((I.filter P).card : ℝ) ≤ rank+d) : by
      classical
      exact t ≤ (I.filter (fun i => ¬ P i)).card

end Lax342547.CoverCounts
