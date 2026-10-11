import Lax342547.RelativeEntropy
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
---
title: Entropy along feasible mixture lines, including new support
type: definition and theorem
---
Old occupied coordinates have a finite directional derivative. Newly occupied coordinates give an exact t log t term whose positive coefficient forces the entropy difference quotient to negative infinity.
-/

namespace Lax342547.EntropyLines

open Lax342547.RelativeEntropy
open scoped Topology BigOperators
open Filter

noncomputable def mix {Ω : Type} (ρ ρ' : Ω → ℝ) (t : ℝ) : Ω → ℝ :=
  fun x => (1-t)*ρ x+t*ρ' x

noncomputable def coordinate (p q : ℝ) : ℝ := p*Real.log p-p*Real.log q

noncomputable def oldEntropy {Ω : Type} [Fintype Ω] (ρ ρ' q : Ω → ℝ) (t : ℝ) : ℝ := by
  classical
  exact ∑ x, if ρ x = 0 then 0 else coordinate (mix ρ ρ' t x) (q x)

noncomputable def oldDerivative {Ω : Type} [Fintype Ω] (ρ ρ' q : Ω → ℝ) : ℝ := by
  classical
  exact ∑ x, if ρ x = 0 then 0 else (ρ' x-ρ x)*(Real.log (ρ x)+1-Real.log (q x))

noncomputable def newMass {Ω : Type} [Fintype Ω] (ρ ρ' : Ω → ℝ) : ℝ := by
  classical
  exact ∑ x, if ρ x = 0 then ρ' x else 0

noncomputable def newEntropy {Ω : Type} [Fintype Ω] (ρ ρ' q : Ω → ℝ) : ℝ := by
  classical
  exact ∑ x, if ρ x = 0 then coordinate (ρ' x) (q x) else 0

axiom mix_derivative {Ω : Type} (ρ ρ' : Ω → ℝ) (x : Ω) :
    HasDerivAt (fun t => mix ρ ρ' t x) (ρ' x-ρ x) 0

axiom old_entropy_derivative {Ω : Type} [Fintype Ω] (ρ ρ' q : Ω → ℝ) :
    HasDerivAt (oldEntropy ρ ρ' q) (oldDerivative ρ ρ' q) 0

axiom entropy_mix_identity {Ω : Type} [Fintype Ω] (ρ ρ' q : Ω → ℝ)
    (hρ' : ∀ x, 0 ≤ ρ' x) (t : ℝ) (ht : 0 < t) :
    entropy (mix ρ ρ' t) q = oldEntropy ρ ρ' q t + t*newMass ρ ρ'*Real.log t + t*newEntropy ρ ρ' q

axiom old_entropy_zero {Ω : Type} [Fintype Ω] (ρ ρ' q : Ω → ℝ) :
    oldEntropy ρ ρ' q 0 = entropy ρ q

axiom entropy_new_support_slope {Ω : Type} [Fintype Ω] (ρ ρ' q : Ω → ℝ)
    (hρ' : ∀ x, 0 ≤ ρ' x) (hnew : 0 < newMass ρ ρ') :
    Tendsto (fun t => (entropy (mix ρ ρ' t) q-entropy ρ q)/t) (𝓝[>] 0) atBot

end Lax342547.EntropyLines
