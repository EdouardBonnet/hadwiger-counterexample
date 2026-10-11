import Lax342547.SampleScales

/-!
---
title: Exponential sampling failure margin
type: definition and theorem
---
At the paper parameters the complete container union budget is eventually at most two to minus half the sample size.
-/

namespace Lax342547.ProbabilityScales

open Lax342547.RawToGraph Lax342547.FingerprintScales Lax342547.ContainerAsymptotics
open Filter

axiom paper_failure_exponential_budget (v A g N : ℕ) (hg : 0 < g) (hN : 0 < N)
    (hv : v ≤ 2^(A*N^2)) (he : 2*exponentBudget A g N+4 ≤ sampleSize g N) :
    (((v^2+1)^fingerprintLength g N : ℕ) : ℝ)*
      exceptionBudget (sampleSize g N) ((sampleSize g N+199)/200) ((2 : ℝ)^1000) ((2 : ℝ)^(4000*g*N)) ≤
        1/(2 : ℝ)^(sampleSize g N/2)

axiom eventually_paper_failure_budget (A g : ℕ) (hg : 0 < g) :
    ∀ᶠ N : ℕ in atTop, ∀ v : ℕ, v ≤ 2^(A*N^2) →
      (((v^2+1)^fingerprintLength g N : ℕ) : ℝ)*
        exceptionBudget (sampleSize g N) ((sampleSize g N+199)/200)
          ((2 : ℝ)^1000) ((2 : ℝ)^(4000*g*N)) ≤ 1/(2 : ℝ)^(sampleSize g N/2)

end Lax342547.ProbabilityScales
