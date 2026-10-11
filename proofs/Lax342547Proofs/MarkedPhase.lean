import Lax342547.MarkedPhase
import Lax342547Proofs.PhaseAverages

namespace Lax342547Proofs.MarkedPhase
open Lax342547.MarkedPhase

set_option backward.isDefEq.respectTransparency false
open Lax342547.MomentSpace Lax342547.RawFrames Lax342547.ChannelDensity Lax342547.ChannelCharacters
open Lax342547.RealCellLaws Lax342547.FiniteSampling Lax342547.TensorCharacters
open Lax342547.PushforwardWalsh Lax342547.RetainedImages Lax342547.ChannelColumns
open Lax342547.RelativeEntropy Lax342547.ComponentSpaces Lax342547.ComponentDuals Lax342547.CoverProjection
open scoped BigOperators

/--
---
conclusion: Lax342547.MarkedPhase.no_cover_marked_unit_phase
---
-/
theorem no_cover_marked_unit_phase {e B N Ω U : Type} [Fintype e] [Fintype B] [Fintype N] [Fintype Ω] [Fintype U]
    [DecidableEq e] [DecidableEq N] (E : Matrix B B Binary)
    (μ : Ω → ℝ) (A : Ω → e → Matrix N N Binary) (ψ : (e → Matrix N N Binary) → Ω → ℝ) (r h t k : ℕ) (p θ : ℝ)
    [Nonempty (Frame B (Fin h) N E)] (hN : 2*h+1 ≤ Fintype.card N)
    (hμ : Probability μ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hr : 1 ≤ r)
    (hA : ∀ x, ∑ i, (A x i).rank ≤ r) (hψ : ∀ S, (∑ i, (S i).rank) ≤ r → ∀ x, |ψ S x| ≤ 1)
    (hsize : 2*t = 2^k) (hk : 100*r+12 ≤ k) (hθ : 0 < θ)
    (β : U → ℝ) (image : U → e → Frame B (Fin h) N E) (L : ℝ)
    (S : U → e → Matrix N N Binary)
    (hβ : Probability β) (hL : 0 ≤ L)
    (hβcap : ∀ o, push β image o ≤ L*weights (Lax342547.RawLaw.uniformLaw E) o)
    (hS : ∀ o, (∑ i, (S o i).rank) ≤ r)
    (hcover : ∀ S : Submodule Binary (e → N → Binary),
      ∀ T : Submodule Binary (Module.Dual Binary (e → N → Binary)),
      Componentwise S → DualComponentwise T →
      (Module.finrank Binary S : ℝ) ≤ (r : ℝ)*(2*t) →
      (Module.finrank Binary T : ℝ) ≤ (r : ℝ)*(2*t) →
      cellMass μ (fun x => projection (LinearMap.piMap (fun i => (A x i).mulVecLin)) S T = 0) ≤ p) :
    |∑ o, β o*(∑ x, μ x*ψ (S o) x*tensorCharacter h (A x) (columnsEquiv h (fun a => channels (image o a))))| ≤
      θ+L*((r+1 : ℝ)^Fintype.card e*(2 : ℝ)^(2*Fintype.card N*r)*
        (2 : ℝ)^(Fintype.card e*(h*h+2))*
        (((4 : ℝ)^(2*t)*p^(2^(k-(100*r+10)))+1/(2 : ℝ)^(h*2^(k-(100*r+12))))/θ^(2*t))) := by
  classical
  let f := fun o : U =>
    ∑ x, μ x*ψ (S o) x*tensorCharacter h (A x) (columnsEquiv h (fun a => channels (image o a)))
  let bad := fun o : e → Frame B (Fin h) N E => ∃ T : e → Matrix N N Binary,
    (∑ i, (T i).rank) ≤ r ∧
      θ ≤ |∑ x, μ x*ψ T x*tensorCharacter h (A x) (columnsEquiv h (fun a => channels (o a)))|
  have hh := Lax342547Proofs.PhaseAverages.average_from_phase_tail β f θ hβ
    (fun o => Lax342547Proofs.PhaseAverages.conditional_phase_abs_le_one μ A (ψ (S o)) h _ hμ (hψ (S o) (hS o))) hθ.le
  have hbad := Lax342547Proofs.FiniteSampling.cell_mass_mono β (fun o => θ ≤ |f o|)
    (fun o => bad (image o)) hβ.1 (fun o ho => ⟨S o,hS o,ho⟩)
  rw [← Lax342547Proofs.ChannelColumns.push_cell_mass β image bad] at hbad
  have hd := Lax342547Proofs.PhaseAverages.finite_event_density
    (weights (Lax342547.RawLaw.uniformLaw E)) (push β image) L hβcap bad
  have ht := Lax342547Proofs.UniformPhaseTails.no_cover_uniform_target_tail E μ A ψ
    r h t k p θ hN hμ hp0 hp1 hr hA hψ hsize hk hθ hcover
  exact hh.trans (add_le_add le_rfl (hbad.trans (hd.trans (mul_le_mul_of_nonneg_left ht hL))))

end Lax342547Proofs.MarkedPhase
