import Lax342547.PaperGraphTransfer
import Lax342547.FingerprintScales
import Lax342547.RawToGraph
import Lax342547.SampleScales

namespace Lax342547Proofs.PaperGraphTransfer
open Lax342547.PaperGraphTransfer

set_option backward.isDefEq.respectTransparency false
open Lax342547.RelativeEntropy Lax342547.UnitLaws Lax342547.ContainerLaws
open Lax342547.MatchingSamples Lax342547.SampledGraph Lax342547.ConnectedMatching
open Lax342547.FingerprintScales Lax342547.ContainerAsymptotics
open Filter

/--
---
conclusion: Lax342547.PaperGraphTransfer.paper_graph_transfer
---
-/
theorem paper_graph_transfer {Ω : ℕ → Type} [∀ N, Fintype (Ω N)] [∀ N, Nonempty (Ω N)]
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
      100*connectedMatchingNumber (sampleGraph (hole N) (hsymm N) sample) < sampleSize g N := by
  filter_upwards [hcard,hsuper,Lax342547.SampleScales.eventually_paper_sampling_budget A g hg,
    eventually_ge_atTop 1] with N hc hs hb hN
  have hn : 0 < N := by omega
  have he1 : 1/(2 : ℝ)^(100*g*N) < 1 := by
    apply (div_lt_one (by positivity)).mpr
    exact one_lt_pow₀ (by norm_num) (by positivity)
  have hm : sampleSize g N ≠ 0 := by unfold sampleSize; positivity
  have hscale := Lax342547.FingerprintScales.paper_sample_ceiling (sampleSize g N)
  apply Lax342547.RawToGraph.supersaturation_to_sample (μ N) (hole N)
    (hsymm N) (hloop N) (htriangle N) ((2 : ℝ)^1000) ((2 : ℝ)^(4000*g*N))
    (1/(2 : ℝ)^(100*g*N)) (sampleSize g N) ((sampleSize g N+199)/200) (fingerprintLength g N)
    (hμ N) (hμpos N) (by positivity) (by positivity) (by positivity) he1
    (Lax342547.FingerprintScales.paper_fingerprint_length g N hg hn)
    (hscale.resolve_right hm) (hb _ hc) hs

end Lax342547Proofs.PaperGraphTransfer
