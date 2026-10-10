import Lax342547.CollisionExponents
import Lax342547.PairRecovery

/-!
---
title: Quantitative collision and squared restriction exponents
type: definition and theorem
---
Explicit scale conditions put pruning below half the accepted overlap. The surviving key collision and scalar agreement yield a proved exponential lower bound, and squared restriction recovery preserves the original-law cost.
-/

namespace Lax342547.CollisionCosts



axiom pruning_half_overlap (η N overlap : ℝ)
    (hscale : 1 ≤ (1/200-η)*N) (hoverlap : (2:ℝ)^(-η*N) ≤ overlap) :
    (2:ℝ)^(-N/200) ≤ overlap/2

axiom collision_exponential_lower (k η N keys overlap error agreement holes : ℝ)
    (hkeys : 0 < keys) (hkeybound : keys ≤ (2:ℝ)^(k*N))
    (hoverlap : (2:ℝ)^(-η*N) ≤ overlap)
    (herror : error ≤ (2:ℝ)^(-N/200)) (hscale : 1 ≤ (1/200-η)*N)
    (hagreement : (2:ℝ)^(-N/50) ≤ agreement)
    (hholes : agreement*(overlap-error)/keys ≤ holes) :
    (2:ℝ)^(-((k+1/50+η)*N)-1) ≤ holes

axiom restriction_exponential_lower (k η N mass restricted original : ℝ)
    (hmass : (2:ℝ)^(-η*N) ≤ mass)
    (hrestricted : (2:ℝ)^(-((k+1/50+η)*N)-1) ≤ restricted)
    (hrecovery : mass^2*restricted ≤ original) :
    (2:ℝ)^(-((k+1/50+3*η)*N)-1) ≤ original

end Lax342547.CollisionCosts
