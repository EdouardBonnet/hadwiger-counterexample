import Lax342547.RetainedImages

/-!
---
title: Explicit pruning and scalar agreement exponent margins
type: lemma
---
The numerical bounds in the collision argument have explicit scale conditions. Original-cell pruning is exponentially smaller than overlap, and the actual scalar tests cost at most .02N when their bit count is at most .01N.
-/

namespace Lax342547.CollisionExponents



axiom pruning_power_identity (k Cn N : ℝ) :
    2 * (2 : ℝ)^(k*N) * (2 : ℝ)^Cn * (2 : ℝ)^(-(k+1/100)*N) =
      (2 : ℝ)^(1+Cn-N/100)

axiom pruning_overlap_bound (keyCount cellCount k Cn N : ℝ)
    (_hkey0 : 0 ≤ keyCount) (hcell0 : 0 ≤ cellCount)
    (hkey : keyCount ≤ (2 : ℝ)^(k*N)) (hcell : cellCount ≤ (2 : ℝ)^Cn)
    (hscale : 1+Cn ≤ N/200) :
    2 * keyCount * cellCount * (2 : ℝ)^(-(k+1/100)*N) ≤ (2 : ℝ)^(-N/200)

axiom scalar_agreement_power (s : ℕ) :
    1 / (2 : ℝ)^(s+1) = (2 : ℝ)^(-((s : ℝ)+1))

axiom paper_scalar_smallness (s : ℕ) (N : ℝ) (hs : (s : ℝ) ≤ N/100) (hN : 100 ≤ N) :
    (2 : ℝ)^(-(45/100 : ℝ)*N) ≤ 1/(2 : ℝ)^(s+1)

axiom paper_scalar_cost (s : ℕ) (N : ℝ) (hs : (s : ℝ) ≤ N/100) (hN : 100 ≤ N) :
    (2 : ℝ)^(-N/50) ≤ 1/(2 : ℝ)^(s+1)

axiom collision_lower_from_overlap (overlap retained error keys agreement holes : ℝ)
    (hkeys : 0 < keys) (hagreement : 0 ≤ agreement)
    (hpruning : overlap - keys * retained ≤ error)
    (hholes : agreement * retained ≤ holes) :
    agreement * (overlap-error) / keys ≤ holes

end Lax342547.CollisionExponents
