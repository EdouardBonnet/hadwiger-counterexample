import Lax342547.SampleScales

/-!
---
title: Supersaturation to sampled graphs at the paper parameters
type: lemma
---
For any finite raw family with a uniform quadratic logarithmic alphabet bound and the actual raw-unit supersaturation property, the paper parameter choices give good sampled graphs for every sufficiently large ambient dimension. This conditional transfer permits repeated raw samples and bounds the actual connected matching number.
-/

namespace Lax342547.PaperGraphTransfer

open Lax342547.RelativeEntropy Lax342547.UnitLaws Lax342547.ContainerLaws
open Lax342547.MatchingSamples Lax342547.SampledGraph Lax342547.ConnectedMatching
open Lax342547.FingerprintScales Lax342547.ContainerAsymptotics
open Filter

axiom paper_graph_transfer {Ω : ℕ → Type} [∀ N, Fintype (Ω N)] [∀ N, Nonempty (Ω N)]
    (μ : ∀ N, Ω N → ℝ) (hole : ∀ N, Ω N → Ω N → Prop) (A g : ℕ) (hg : 0 < g)
    (hsymm : ∀ N, ∀ ⦃x y⦄, hole N x y → hole N y x)
    (hloop : ∀ N x, ¬ hole N x x)
    (htriangle : ∀ N x y z, hole N x y → hole N y z → ¬ hole N z x)
    (hμ : ∀ N, Probability (μ N)) (hμpos : ∀ N x, 0 < μ N x)
    (hcard : ∀ᶠ N : ℕ in atTop, Fintype.card (Ω N) ≤ 2^(A*N^2))
    (hsuper : ∀ᶠ N : ℕ in atTop, ∀ ρ,
      Feasible (μ N) (fun x y => ¬ hole N x y) ((2 : ℝ)^1000) ((2 : ℝ)^(4000*g*N)) ρ →
      1/(2 : ℝ)^(100*g*N) ≤ conflictMass ρ (fourConflict (hole N))) :
    ∀ᶠ N : ℕ in atTop, ∃ sample : Fin (sampleSize g N) → Ω N,
      (sampleGraph (hole N) (hsymm N) sample).indepNum ≤ 2 ∧
      100*connectedMatchingNumber (sampleGraph (hole N) (hsymm N) sample) < sampleSize g N

end Lax342547.PaperGraphTransfer
