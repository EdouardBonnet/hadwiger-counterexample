import Lax342547.FingerprintScales
import Lax342547.ContainerAsymptotics

/-!
---
title: Eventual sampling margins for the paper parameters
type: definition and theorem
---
The raw alphabet bound and explicit fingerprint length give a strict total sampling budget for all sufficiently large ambient dimensions, uniformly over raw spaces satisfying the same quadratic logarithmic size bound.
-/

namespace Lax342547.SampleScales

open Lax342547.RawToGraph Lax342547.FingerprintScales Lax342547.ContainerAsymptotics
open Filter

axiom raw_alphabet_bound (v A N : ℕ) (hv : v ≤ 2^(A*N^2)) :
    v^2+1 ≤ 2^(2*A*N^2+1)

axiom raw_fingerprint_count_bound (v A g N : ℕ) (hv : v ≤ 2^(A*N^2)) :
    (v^2+1)^fingerprintLength g N ≤ 2^(exponentBudget A g N)

axiom paper_sampling_budget (v A g N : ℕ) (hg : 0 < g) (hN : 0 < N)
    (hv : v ≤ 2^(A*N^2)) (he : exponentBudget A g N+2 < sampleSize g N) :
    (((v^2+1)^fingerprintLength g N : ℕ) : ℝ)*
      exceptionBudget (sampleSize g N) ((sampleSize g N+199)/200) ((2 : ℝ)^1000) ((2 : ℝ)^(4000*g*N)) < 1

axiom eventually_paper_sampling_budget (A g : ℕ) (hg : 0 < g) :
    ∀ᶠ N : ℕ in atTop, ∀ v : ℕ, v ≤ 2^(A*N^2) →
      (((v^2+1)^fingerprintLength g N : ℕ) : ℝ)*
        exceptionBudget (sampleSize g N) ((sampleSize g N+199)/200)
          ((2 : ℝ)^1000) ((2 : ℝ)^(4000*g*N)) < 1

end Lax342547.SampleScales
