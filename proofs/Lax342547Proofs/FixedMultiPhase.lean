import Lax342547.FixedMultiPhase
import Lax342547Proofs.MultiChannelPhase
import Lax342547Proofs.DyadicMoments
import Lax342547Proofs.DyadicMoments

namespace Lax342547Proofs.FixedMultiPhase

open Lax342547.FixedMultiPhase

set_option backward.isDefEq.respectTransparency false
open Lax342547.MomentSpace Lax342547.RawFrames Lax342547.ChannelDensity Lax342547.ChannelCharacters
open Lax342547.RealCellLaws Lax342547.FiniteSampling Lax342547.TensorCharacters
open Lax342547.PushforwardWalsh Lax342547.RetainedImages Lax342547.ChannelColumns
open Lax342547.RelativeEntropy Lax342547.ComponentSpaces Lax342547.ComponentDuals Lax342547.CoverProjection
open scoped BigOperators

/--
---
conclusion: Lax342547.FixedMultiPhase.fixed_parameter_marked_unit_phase
---
-/
theorem fixed_parameter_marked_unit_phase {e d B N Ω U : Type} [Fintype e] [Fintype d] [Nonempty d] [Fintype U] [Fintype B] [Fintype N] [Fintype Ω]
    [DecidableEq e] [DecidableEq d] [DecidableEq N] (E : Matrix B B Binary)
    (μ : Ω → ℝ) (A : Ω → e → Matrix N N Binary) (ψ : (e → Matrix N N Binary) → Ω → ℝ) (r h a c Γ P : ℕ)
    [Nonempty (Frame B (Fin h) N E)] (hN : 2*h+1 ≤ Fintype.card N)
    (hμ : Probability μ) (hr : 1 ≤ r)
    (hA : ∀ x, ∑ i, (A x i).rank ≤ r) (hψ : ∀ S, (∑ i, (S i).rank) ≤ r → ∀ x, |ψ S x| ≤ 1)
    (hc : 0 < c) (hscale : c*2^(100*r+12) ≤ Fintype.card N)
    (hP : 2^(100*r+10)*(2+a+Γ*(2*c)+1) ≤ P)
    (hh : 4*2^(100*r+10)*(a+Γ*(2*c)+1) ≤ h)
    (β : U → ℝ) (image : U → (e × d) → Frame B (Fin h) N E) (L : ℝ)
    (S : U → e → Matrix N N Binary)
    (hβ : Probability β) (hL : 0 ≤ L)
    (hβcap : ∀ o, push β image o ≤ L*weights (Lax342547.RawLaw.uniformLaw E) o)
    (hS : ∀ o, (∑ i, (S o i).rank) ≤ r)
    (hcover : ∀ S : Submodule Binary (e → N → Binary),
      ∀ T : Submodule Binary (Module.Dual Binary (e → N → Binary)),
      Componentwise S → DualComponentwise T →
      (Module.finrank Binary S : ℝ) ≤ (r : ℝ)*(Fintype.card N/c) →
      (Module.finrank Binary T : ℝ) ≤ (r : ℝ)*(Fintype.card N/c) →
      cellMass μ (fun x => projection (LinearMap.piMap (fun i => (A x i).mulVecLin)) S T = 0) ≤ 1/(2 : ℝ)^P) :
    |∑ o, β o*(∑ x, μ x*ψ (S o) x*tensorCharacter h (fun i : e × d => A x i.1) (columnsEquiv h (fun a => channels (image o a))))| ≤
      1/(2 : ℝ)^a+L*((r+1 : ℝ)^Fintype.card e*(2 : ℝ)^(2*Fintype.card N*r)*
        (2 : ℝ)^(Fintype.card (e × d)*(h*h+2))/(2 : ℝ)^(Γ*Fintype.card N)) := by
  classical
  have hs : c*2^((100*r+10)+2) ≤ Fintype.card N := by simpa only [Nat.add_assoc] using hscale
  have hhD : 4*2^(100*r+10)*(a+Γ*(2*c)+1) ≤ Fintype.card d*h :=
    hh.trans (by simpa only [one_mul] using Nat.mul_le_mul_right h ((show 1 ≤ Fintype.card d from Fintype.card_pos_iff.mpr (inferInstance : Nonempty d))))
  obtain ⟨k,t,hk,hsize,hlo,hbudget⟩ :=
    Lax342547Proofs.DyadicMoments.dyadic_budget_with_fixed_parameters c (100*r+10) a Γ P (Fintype.card d*h)
      (Fintype.card N) hc hs hP hhD
  have hm : 2*t ≤ Fintype.card N/c := by
    apply (Nat.le_div_iff_mul_le hc).mpr
    rw [hsize,Nat.mul_comm]
    exact hlo
  have hθ : 0 < 1/(2 : ℝ)^a := by positivity
  have hp0 : 0 ≤ 1/(2 : ℝ)^P := by positivity
  have hp1 : 1/(2 : ℝ)^P ≤ 1 := by
    have hone : (1 : ℝ) ≤ 2^P := one_le_pow₀ (by norm_num)
    simpa only [one_div_one] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hone
  have hcovers : ∀ T : Submodule Binary (e → N → Binary),
      ∀ U : Submodule Binary (Module.Dual Binary (e → N → Binary)),
      Componentwise T → DualComponentwise U →
      (Module.finrank Binary T : ℝ) ≤ (r : ℝ)*(2*t) →
      (Module.finrank Binary U : ℝ) ≤ (r : ℝ)*(2*t) →
      cellMass μ (fun x => projection (LinearMap.piMap (fun i => (A x i).mulVecLin)) T U = 0) ≤ 1/(2 : ℝ)^P := by
    intro T U hT hU hdT hdU
    have hdim : (r : ℝ)*(2*t) ≤ (r : ℝ)*(Fintype.card N/c) := by
      have hcm : (c : ℝ)*(2*t) ≤ (Fintype.card N : ℝ) := by
        exact_mod_cast (show c*(2*t) ≤ Fintype.card N from by rw [hsize]; exact hlo)
      have hcr : (0 : ℝ) < c := by exact_mod_cast hc
      have hs' : (2*(t : ℝ)) ≤ (Fintype.card N : ℝ)/c :=
        (le_div_iff₀ hcr).mpr (by simpa only [mul_comm] using hcm)
      exact mul_le_mul_of_nonneg_left hs' (Nat.cast_nonneg r)
    exact hcover T U hT hU (hdT.trans hdim) (hdU.trans hdim)
  have havg := Lax342547Proofs.MultiChannelPhase.no_cover_marked_unit_phase (d := d) E μ A ψ r h t k
    (1/(2 : ℝ)^P) (1/(2 : ℝ)^a) hN hμ hp0 hp1 hr hA hψ hsize (by omega) hθ
    β image L S hβ hL hβcap hS hcovers
  have hb := mul_le_mul_of_nonneg_left hbudget
    (show 0 ≤ (r+1 : ℝ)^Fintype.card e*(2 : ℝ)^(2*Fintype.card N*r)*(2 : ℝ)^(Fintype.card (e × d)*(h*h+2)) from by positivity)
  have hc' := add_le_add (le_rfl : 1/(2 : ℝ)^a ≤ 1/(2 : ℝ)^a) (mul_le_mul_of_nonneg_left hb hL)
  apply havg.trans
  simpa only [Nat.add_assoc,show (10+2 : ℕ) = 12 from rfl,mul_one_div,mul_div_assoc,mul_one] using hc'

end Lax342547Proofs.FixedMultiPhase
