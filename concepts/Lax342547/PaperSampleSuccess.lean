import Lax342547.PaperGraphProbability
import Lax342547.SampledGraph

/-!
---
title: High probability sampled graph construction
type: definition and theorem
---
Under actual raw supersaturation, the full sampled graph event combining independence number at most two and the connected matching bound has eventual probability at least one minus two to minus half the sample size.
-/

namespace Lax342547.PaperSampleSuccess

open Lax342547.RelativeEntropy Lax342547.UnitLaws Lax342547.ContainerLaws
open Lax342547.MatchingSamples Lax342547.SampledGraph Lax342547.ConnectedMatching
open Lax342547.FingerprintScales Lax342547.FiniteSampling Lax342547.RetainedImages
open Filter

axiom paper_sample_success {Ω : ℕ → Type} [∀ N, Fintype (Ω N)] [∀ N, Nonempty (Ω N)]
    (μ : ∀ N, Ω N → ℝ) (hole : ∀ N, Ω N → Ω N → Prop) (A g : ℕ) (hg : 0 < g)
    (hsymm : ∀ N, ∀ ⦃x y⦄, hole N x y → hole N y x)
    (hloop : ∀ N x, ¬ hole N x x)
    (htriangle : ∀ N x y z, hole N x y → hole N y z → ¬ hole N z x)
    (hμ : ∀ N, Probability (μ N)) (hμpos : ∀ N x, 0 < μ N x)
    (hcard : ∀ᶠ N : ℕ in atTop, Fintype.card (Ω N) ≤ 2^(A*N^2))
    (hsuper : ∀ᶠ N : ℕ in atTop, ∀ ρ,
      Feasible (μ N) (fun x y => ¬ hole N x y) ((2 : ℝ)^1000) ((2 : ℝ)^(4000*g*N)) ρ →
      1/(2 : ℝ)^(100*g*N) ≤ conflictMass ρ (fourConflict (hole N))) :
    ∀ᶠ N : ℕ in atTop,
      1-1/(2 : ℝ)^(sampleSize g N/2) ≤
        cellMass (productLaw (fun _ : Fin (sampleSize g N) => μ N))
          (fun sample => (sampleGraph (hole N) (hsymm N) sample).indepNum ≤ 2 ∧
            100*connectedMatchingNumber (sampleGraph (hole N) (hsymm N) sample) < sampleSize g N)

end Lax342547.PaperSampleSuccess
