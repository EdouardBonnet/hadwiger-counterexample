import Lax342547.UnitContainers
import Lax342547.GoodSamples
import Lax342547.MatchingCoverage

/-!
---
title: Finite supersaturation implies an actual sampled graph
type: lemma
---
The exact admissible raw-unit supersaturation property, together with the explicit entropy, counting and sampling margins, produces a graph on sampled positions with independence number at most two and 100 times its actual connected matching number less than its order.
-/

namespace Lax342547.RawToGraph

open Lax342547.RelativeEntropy Lax342547.UnitLaws Lax342547.ContainerLaws
open Lax342547.RetainedImages Lax342547.CellAveraging Lax342547.FiniteSampling
open Lax342547.GoodSamples Lax342547.MatchingSamples Lax342547.SampledGraph Lax342547.ConnectedMatching

noncomputable def exceptionBudget (m k : ℕ) (M κ : ℝ) : ℝ :=
  (m.choose k : ℝ)*(1/M)^k+(m : ℝ)^(2*k)*(1/κ)^k

axiom exception_budget_nonneg (m k : ℕ) (M κ : ℝ) (hM : 0 < M) (hκ : 0 < κ) :
    0 ≤ exceptionBudget m k M κ

axiom supersaturation_to_sample {Ω : Type} [Fintype Ω] [Nonempty Ω]
    (μ : Ω → ℝ) (hole : Ω → Ω → Prop)
    (hsymm : ∀ ⦃x y⦄, hole x y → hole y x) (hloop : ∀ x, ¬ hole x x)
    (htriangle : ∀ x y z, hole x y → hole y z → ¬ hole z x)
    (M κ ε : ℝ) (m k L : ℕ)
    (hμ : Probability μ) (hμpos : ∀ x, 0 < μ x)
    (hM : 0 < M) (hκ : 0 < κ) (hε : 0 < ε) (hε1 : ε < 1)
    (hL : Real.log κ/(-Real.log (1-ε))+1 ≤ L)
    (hscale : 200*(k-1) < m)
    (hbudget : (((Fintype.card Ω^2+1)^L : ℕ) : ℝ)*exceptionBudget m k M κ < 1)
    (hsuper : ∀ ρ, Feasible μ (fun x y => ¬ hole x y) M κ ρ →
      ε ≤ conflictMass ρ (fourConflict hole)) :
    ∃ sample : Fin m → Ω,
      (sampleGraph hole hsymm sample).indepNum ≤ 2 ∧
      100*connectedMatchingNumber (sampleGraph hole hsymm sample) < m

end Lax342547.RawToGraph
