import Lax342547.RawToGraph
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Analysis.SpecificLimits.Normed

/-!
---
title: The paper fingerprint and exception scales
type: lemma
---
The paper entropy length is bounded by an explicit natural fingerprint length. Coarse binomial counting already gives an exponentially small vertex tail with M = 2^1000, and disjoint pair exceptions obey the corresponding power bound at the paper sample size.
-/

namespace Lax342547.FingerprintScales

open Lax342547.RawToGraph
open Filter

def sampleSize (g N : ℕ) : ℕ := 2^(1000*g*N)
def fingerprintLength (g N : ℕ) : ℕ := 4000*g*N*2^(100*g*N)+2

axiom logarithmic_progress (ε : ℝ) (_hε : 0 < ε) (hε1 : ε < 1) : ε ≤ -Real.log (1-ε)

axiom paper_fingerprint_length (g N : ℕ) (hg : 0 < g) (hN : 0 < N) :
    Real.log ((2 : ℝ)^(4000*g*N))/(-Real.log (1-1/(2 : ℝ)^(100*g*N)))+1 ≤
      fingerprintLength g N

axiom paper_sample_ceiling (m : ℕ) : 200*((m+199)/200-1) < m ∨ m = 0

axiom vertex_exception_power (m k : ℕ) (hk : m ≤ 200*k) :
    (m.choose k : ℝ)*(1/(2 : ℝ)^1000)^k ≤ 1/(2 : ℝ)^m

axiom pair_exception_power (g N k : ℕ) (hg : 0 < g) (hN : 0 < N)
    (hk : sampleSize g N ≤ 200*k) :
    (sampleSize g N : ℝ)^(2*k)*(1/(2 : ℝ)^(4000*g*N))^k ≤ 1/(2 : ℝ)^(sampleSize g N)

end Lax342547.FingerprintScales
