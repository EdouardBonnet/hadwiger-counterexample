import Lax342547.PaperSampleSuccess
import Lax342547.ContainerLaws
import Lax342547.FiniteSampling
import Lax342547.PaperGraphProbability
import Lax342547.SampledGraph

namespace Lax342547Proofs.PaperSampleSuccess
open Lax342547.PaperSampleSuccess

set_option backward.isDefEq.respectTransparency false
open Lax342547.RelativeEntropy Lax342547.UnitLaws Lax342547.ContainerLaws
open Lax342547.MatchingSamples Lax342547.SampledGraph Lax342547.ConnectedMatching
open Lax342547.FingerprintScales Lax342547.FiniteSampling Lax342547.RetainedImages
open Filter

/--
---
conclusion: Lax342547.PaperSampleSuccess.paper_sample_success
---
-/
theorem paper_sample_success {Ω : ℕ → Type} [∀ N, Fintype (Ω N)] [∀ N, Nonempty (Ω N)]
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
            100*connectedMatchingNumber (sampleGraph (hole N) (hsymm N) sample) < sampleSize g N) := by
  filter_upwards [Lax342547.PaperGraphProbability.paper_graph_failure_probability μ hole A g hg
    hsymm hloop hμ hμpos hcard hsuper] with N hf
  let ν := productLaw (fun _ : Fin (sampleSize g N) => μ N)
  let Bad := fun sample : Fin (sampleSize g N) → Ω N =>
    sampleSize g N ≤ 100*connectedMatchingNumber (sampleGraph (hole N) (hsymm N) sample)
  have hprob := Lax342547.FiniteSampling.product_probability
    (fun _ : Fin (sampleSize g N) => μ N) (fun _ => hμ N)
  have hcomp := Lax342547.ContainerLaws.mass_complement ν Bad hprob
  have he : (fun sample : Fin (sampleSize g N) → Ω N => ¬ Bad sample) =
      (fun sample => (sampleGraph (hole N) (hsymm N) sample).indepNum ≤ 2 ∧
        100*connectedMatchingNumber (sampleGraph (hole N) (hsymm N) sample) < sampleSize g N) := by
    funext sample
    apply propext
    have hi := Lax342547.SampledGraph.sampleGraph_indepNum_le_two (hole N) (hsymm N) (htriangle N) sample
    simp only [Bad,not_le]
    exact ⟨fun hh => ⟨hi,hh⟩,fun hh => hh.2⟩
  rw [← he]
  linarith

end Lax342547Proofs.PaperSampleSuccess
