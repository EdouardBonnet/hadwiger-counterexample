import Lax342547.CollisionCosts

/-!
---
title: Uniform collision scales and bounded numerical options
type: definition and theorem
---
A fixed ambient multiplier pays linear record and scalar bit costs. An explicit overlap threshold controls pruning, and a finite option sum has a witnessed option with its precise exponent cost.
-/

namespace Lax342547.CollisionScales



axiom record_scale (C M₀ n : ℝ) (hn : 1 ≤ n) (hM : 200*(C+1) ≤ M₀) :
    1+C*n ≤ M₀*n/200

axiom scalar_scale (c M₀ n : ℝ) (hn : 0 ≤ n) (hM : 100*c ≤ M₀)
    (s : ℕ) (hs : (s:ℝ) ≤ c*n) : (s:ℝ) ≤ M₀*n/100

axiom eventual_pruning_gap (η : ℝ) (hη : η < 1/200) :
    ∃ N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N → 100 ≤ N ∧ 1 ≤ (1/200-η)*N

axiom bounded_options {O : Type} [Fintype O] [Nonempty O]
    (f : O → ℝ) (overlap : ℝ) (h : overlap ≤ ∑ o, f o) :
    ∃ o, overlap / Fintype.card O ≤ f o

axiom bounded_option_exponent (cost δ N options probability : ℝ)
    (hoptions : 0 < options) (hcount : options ≤ (2:ℝ)^(δ*N))
    (hprobability : (2:ℝ)^(-cost*N)/options ≤ probability) :
    (2:ℝ)^(-(cost+δ)*N) ≤ probability

end Lax342547.CollisionScales
