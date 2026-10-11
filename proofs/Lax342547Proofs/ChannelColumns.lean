import Lax342547.ChannelColumns
import Lax342547Proofs.ChannelDensity
import Lax342547Proofs.NoCoverMoments
import Lax342547Proofs.RealCellLaws

namespace Lax342547Proofs.ChannelColumns
open Lax342547.ChannelColumns

set_option backward.isDefEq.respectTransparency false
open Lax342547.MomentSpace Lax342547.RawFrames Lax342547.ChannelDensity Lax342547.ChannelCharacters
open Lax342547.RealCellLaws Lax342547.FiniteSampling Lax342547.TensorCharacters
open Lax342547.PushforwardWalsh Lax342547.RetainedImages
open Lax342547.RelativeEntropy Lax342547.ComponentSpaces Lax342547.ComponentDuals Lax342547.CoverProjection
open scoped BigOperators

/--
---
conclusion: Lax342547.ChannelColumns.columns_uniform_weights
---
-/
theorem columns_uniform_weights {e N : Type} [Fintype e] [Fintype N] [DecidableEq e] [DecidableEq N] (h : ℕ)
    (z : e → Matrix N (Fin h) Binary × Matrix N (Fin h) Binary) :
    weights (PMF.uniformOfFintype (e → Matrix N (Fin h) Binary × Matrix N (Fin h) Binary)) z =
      productLaw (fun _ : e × Fin h => channelLaw) (columnsEquiv h z) := by
  classical
  simp only [weights,PMF.uniformOfFintype_apply,ENNReal.toReal_inv,ENNReal.toReal_natCast,
    productLaw,channelLaw,Finset.prod_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin]
  simp only [Matrix, Fintype.card_fun,Fintype.card_prod,ZMod.card,Nat.cast_pow,Nat.cast_mul,Nat.cast_ofNat]
  simp only [Fintype.card_fin,← pow_add,one_div,inv_pow,← pow_mul]
  congr 2
  ring

/--
---
conclusion: Lax342547.ChannelColumns.pmf_weights_map
---
-/
theorem pmf_weights_map {Ω X : Type} [Fintype Ω] (p : PMF Ω) (f : Ω → X) (x : X) :
    weights (p.map f) x = push (weights p) f x := by
  classical
  simp only [weights,PMF.map_apply,tsum_fintype]
  rw [ENNReal.toReal_sum (fun o _ => by split_ifs; exact p.apply_ne_top o; exact ENNReal.zero_ne_top)]
  unfold push
  apply Finset.sum_congr rfl
  intro o _
  by_cases hx : x = f o
  · subst x
    simp [weights]
  · simp only [hx,Ne.symm hx,ite_false,ENNReal.toReal_zero]

/--
---
conclusion: Lax342547.ChannelColumns.push_cell_mass
---
-/
theorem push_cell_mass {Ω X : Type} [Fintype Ω] [Fintype X]
    (ρ : Ω → ℝ) (f : Ω → X) (P : X → Prop) :
    cellMass (push ρ f) P = cellMass ρ (fun o => P (f o)) := by
  classical
  have hh := Lax342547Proofs.PushforwardWalsh.push_integral ρ f (fun x => if P x then 1 else 0)
  simpa [cellMass,mul_ite] using hh

/--
---
conclusion: Lax342547.ChannelColumns.raw_channel_point_cap
---
-/
theorem raw_channel_point_cap {e B N : Type} [Fintype e] [Fintype B] [Fintype N]
    [DecidableEq e] [DecidableEq N] (h : ℕ) (E : Matrix B B Binary)
    [Nonempty (Frame B (Fin h) N E)] (hN : 2*h+1 ≤ Fintype.card N)
    (z : e → Matrix N (Fin h) Binary × Matrix N (Fin h) Binary) :
    weights ((Lax342547.RawLaw.uniformLaw E).map (fun o a => channels (o a))) z ≤
      (2 : ℝ)^(Fintype.card e*(h*h+2))*
        productLaw (fun _ : e × Fin h => channelLaw) (columnsEquiv h z) := by
  have hh := Lax342547Proofs.ChannelDensity.all_components_density E (by simp only [Fintype.card_fin]; omega) z
  have hfin : (2 : ENNReal)^(Fintype.card e*(h*h+2))*
      PMF.uniformOfFintype (e → Matrix N (Fin h) Binary × Matrix N (Fin h) Binary) z ≠ ⊤ := ENNReal.mul_ne_top (by simp) (PMF.apply_ne_top _ _)
  simp only [Fintype.card_fin] at hh
  have ht := ENNReal.toReal_mono hfin hh
  rw [← columns_uniform_weights h z]
  simpa only [weights,ENNReal.toReal_mul,ENNReal.toReal_pow,ENNReal.toReal_ofNat] using ht

/--
---
conclusion: Lax342547.ChannelColumns.raw_channel_event_cap
---
-/
theorem raw_channel_event_cap {e B N : Type} [Fintype e] [Fintype B] [Fintype N]
    [DecidableEq e] [DecidableEq N] (h : ℕ) (E : Matrix B B Binary)
    [Nonempty (Frame B (Fin h) N E)] (hN : 2*h+1 ≤ Fintype.card N)
    (P : (e × Fin h → (N → Binary) × (N → Binary)) → Prop) :
    cellMass (weights (Lax342547.RawLaw.uniformLaw E))
      (fun o => P (columnsEquiv h (fun a => channels (o a)))) ≤
      (2 : ℝ)^(Fintype.card e*(h*h+2))*cellMass (productLaw (fun _ : e × Fin h => channelLaw)) P := by
  classical
  let f := fun o : e → Frame B (Fin h) N E => fun a => channels (o a)
  rw [← push_cell_mass (weights (Lax342547.RawLaw.uniformLaw E)) f (fun z => P (columnsEquiv h z))]
  have he : cellMass (productLaw (fun _ : e × Fin h => channelLaw)) P =
      ∑ z : e → Matrix N (Fin h) Binary × Matrix N (Fin h) Binary,
        if P (columnsEquiv h z) then productLaw (fun _ : e × Fin h => channelLaw) (columnsEquiv h z) else 0 := by
    unfold cellMass
    exact ((columnsEquiv (e := e) (N := N) h).sum_comp _).symm
  rw [he,Finset.mul_sum]
  unfold cellMass
  apply Finset.sum_le_sum
  intro z _
  rw [← pmf_weights_map]
  by_cases hz : P (columnsEquiv h z)
  · simp only [hz,ite_true]
    exact raw_channel_point_cap h E hN z
  · simp [hz]

/--
---
conclusion: Lax342547.ChannelColumns.no_cover_raw_phase_tail
---
-/
theorem no_cover_raw_phase_tail {e B N Ω : Type} [Fintype e] [Fintype B] [Fintype N] [Fintype Ω]
    [DecidableEq e] [DecidableEq N] (E : Matrix B B Binary)
    (μ : Ω → ℝ) (A : Ω → e → Matrix N N Binary) (ψ : Ω → ℝ) (r h t k : ℕ) (p θ : ℝ)
    [Nonempty (Frame B (Fin h) N E)] (hN : 2*h+1 ≤ Fintype.card N)
    (hμ : Probability μ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hr : 1 ≤ r)
    (hA : ∀ x, ∑ i, (A x i).rank ≤ r) (hψ : ∀ x, |ψ x| ≤ 1)
    (hsize : 2*t = 2^k) (hk : 100*r+12 ≤ k) (hθ : 0 < θ)
    (hcover : ∀ S : Submodule Binary (e → N → Binary),
      ∀ T : Submodule Binary (Module.Dual Binary (e → N → Binary)),
      Componentwise S → DualComponentwise T →
      (Module.finrank Binary S : ℝ) ≤ (r : ℝ)*(2*t) →
      (Module.finrank Binary T : ℝ) ≤ (r : ℝ)*(2*t) →
      cellMass μ (fun x => projection (LinearMap.piMap (fun i => (A x i).mulVecLin)) S T = 0) ≤ p) :
    cellMass (weights (Lax342547.RawLaw.uniformLaw E))
      (fun o => θ ≤ |∑ x, μ x*ψ x*tensorCharacter h (A x) (columnsEquiv h (fun a => channels (o a)))|) ≤
      (2 : ℝ)^(Fintype.card e*(h*h+2))*
        (((4 : ℝ)^(2*t)*p^(2^(k-(100*r+10)))+1/(2 : ℝ)^(h*2^(k-(100*r+12))))/θ^(2*t)) := by
  have hh := raw_channel_event_cap h E hN
    (fun c => θ ≤ |∑ x, μ x*ψ x*tensorCharacter h (A x) c|)
  exact hh.trans (mul_le_mul_of_nonneg_left
    (Lax342547Proofs.NoCoverMoments.no_cover_phase_tail μ A ψ r h t k p θ hμ hp0 hp1 hr hA hψ hsize hk hcover hθ)
    (by positivity))

end Lax342547Proofs.ChannelColumns
