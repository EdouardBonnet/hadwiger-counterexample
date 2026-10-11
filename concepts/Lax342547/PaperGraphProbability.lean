import Lax342547.GraphFailure
import Lax342547.ProbabilityScales

/-!
---
title: Paper parameter graph probability
type: lemma
---
The failure probability of the connected matching bound is eventually at most two to minus half the sample size, assuming actual raw supersaturation.
-/

namespace Lax342547.PaperGraphProbability

open Lax342547.RelativeEntropy Lax342547.UnitLaws Lax342547.ContainerLaws
open Lax342547.MatchingSamples Lax342547.SampledGraph Lax342547.ConnectedMatching
open Lax342547.FingerprintScales Lax342547.FiniteSampling Lax342547.RetainedImages
open Filter

axiom paper_graph_failure_probability {Ω : ℕ → Type} [∀ N, Fintype (Ω N)] [∀ N, Nonempty (Ω N)]
    (μ : ∀ N, Ω N → ℝ) (hole : ∀ N, Ω N → Ω N → Prop) (A g : ℕ) (hg : 0 < g)
    (hsymm : ∀ N, ∀ ⦃x y⦄, hole N x y → hole N y x)
    (hloop : ∀ N x, ¬ hole N x x)
    (hμ : ∀ N, Probability (μ N)) (hμpos : ∀ N x, 0 < μ N x)
    (hcard : ∀ᶠ N : ℕ in atTop, Fintype.card (Ω N) ≤ 2^(A*N^2))
    (hsuper : ∀ᶠ N : ℕ in atTop, ∀ ρ,
      Feasible (μ N) (fun x y => ¬ hole N x y) ((2 : ℝ)^1000) ((2 : ℝ)^(4000*g*N)) ρ →
      1/(2 : ℝ)^(100*g*N) ≤ conflictMass ρ (fourConflict (hole N))) :
    ∀ᶠ N : ℕ in atTop,
      cellMass (productLaw (fun _ : Fin (sampleSize g N) => μ N))
        (fun sample => sampleSize g N ≤ 100*connectedMatchingNumber (sampleGraph (hole N) (hsymm N) sample)) ≤
          1/(2 : ℝ)^(sampleSize g N/2)

end Lax342547.PaperGraphProbability
