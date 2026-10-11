import Lax342547.UniformPhaseTails
import Lax342547.ChannelColumns
import Lax342547.FiniteSampling
import Lax342547.RealCellLaws
import Lax342547.TotalRankCount

namespace Lax342547Proofs.UniformPhaseTails
open Lax342547.UniformPhaseTails

set_option backward.isDefEq.respectTransparency false
open Lax342547.MomentSpace Lax342547.RawFrames Lax342547.ChannelDensity Lax342547.ChannelCharacters
open Lax342547.RealCellLaws Lax342547.FiniteSampling Lax342547.TensorCharacters
open Lax342547.PushforwardWalsh Lax342547.RetainedImages Lax342547.ChannelColumns
open Lax342547.RelativeEntropy Lax342547.ComponentSpaces Lax342547.ComponentDuals Lax342547.CoverProjection
open scoped BigOperators

/--
---
conclusion: Lax342547.UniformPhaseTails.no_cover_raw_family_tail
---
-/
theorem no_cover_raw_family_tail {e B N Ω C : Type} [Fintype e] [Fintype B] [Fintype N] [Fintype Ω] [Fintype C]
    [DecidableEq e] [DecidableEq N] (E : Matrix B B Binary)
    (μ : Ω → ℝ) (A : Ω → e → Matrix N N Binary) (ψ : C → Ω → ℝ) (r h t k : ℕ) (p θ : ℝ)
    [Nonempty (Frame B (Fin h) N E)] (hN : 2*h+1 ≤ Fintype.card N)
    (hμ : Probability μ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hr : 1 ≤ r)
    (hA : ∀ x, ∑ i, (A x i).rank ≤ r) (hψ : ∀ c x, |ψ c x| ≤ 1)
    (hsize : 2*t = 2^k) (hk : 100*r+12 ≤ k) (hθ : 0 < θ)
    (hcover : ∀ S : Submodule Binary (e → N → Binary),
      ∀ T : Submodule Binary (Module.Dual Binary (e → N → Binary)),
      Componentwise S → DualComponentwise T →
      (Module.finrank Binary S : ℝ) ≤ (r : ℝ)*(2*t) →
      (Module.finrank Binary T : ℝ) ≤ (r : ℝ)*(2*t) →
      cellMass μ (fun x => projection (LinearMap.piMap (fun i => (A x i).mulVecLin)) S T = 0) ≤ p) :
    cellMass (weights (Lax342547.RawLaw.uniformLaw E))
      (fun o => ∃ c : C, θ ≤ |∑ x, μ x*ψ c x*tensorCharacter h (A x) (columnsEquiv h (fun a => channels (o a)))|) ≤
      (Fintype.card C : ℝ)*(2 : ℝ)^(Fintype.card e*(h*h+2))*
        (((4 : ℝ)^(2*t)*p^(2^(k-(100*r+10)))+1/(2 : ℝ)^(h*2^(k-(100*r+12))))/θ^(2*t)) := by
  classical
  let P := fun c : C => fun o : e → Frame B (Fin h) N E =>
    θ ≤ |∑ x, μ x*ψ c x*tensorCharacter h (A x) (columnsEquiv h (fun a => channels (o a)))|
  have hu := Lax342547.FiniteSampling.cell_mass_union_bound
    (weights (Lax342547.RawLaw.uniformLaw E)) P Finset.univ
    (Lax342547.RealCellLaws.weights_nonneg _)
  simp only [Finset.mem_univ,true_and] at hu
  have hloc (c : C) := Lax342547.ChannelColumns.no_cover_raw_phase_tail E μ A (ψ c)
    r h t k p θ hN hμ hp0 hp1 hr hA (hψ c) hsize hk hθ hcover
  calc
    _ ≤ ∑ c, cellMass (weights (Lax342547.RawLaw.uniformLaw E)) (P c) := hu
    _ ≤ ∑ _ : C, (2 : ℝ)^(Fintype.card e*(h*h+2))*
        (((4 : ℝ)^(2*t)*p^(2^(k-(100*r+10)))+1/(2 : ℝ)^(h*2^(k-(100*r+12))))/θ^(2*t)) :=
      Finset.sum_le_sum (fun c _ => hloc c)
    _ = _ := by simp; ring

/--
---
conclusion: Lax342547.UniformPhaseTails.no_cover_uniform_target_tail
---
-/
theorem no_cover_uniform_target_tail {e B N Ω : Type} [Fintype e] [Fintype B] [Fintype N] [Fintype Ω]
    [DecidableEq e] [DecidableEq N] (E : Matrix B B Binary)
    (μ : Ω → ℝ) (A : Ω → e → Matrix N N Binary) (ψ : (e → Matrix N N Binary) → Ω → ℝ) (r h t k : ℕ) (p θ : ℝ)
    [Nonempty (Frame B (Fin h) N E)] (hN : 2*h+1 ≤ Fintype.card N)
    (hμ : Probability μ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hr : 1 ≤ r)
    (hA : ∀ x, ∑ i, (A x i).rank ≤ r) (hψ : ∀ S, (∑ i, (S i).rank) ≤ r → ∀ x, |ψ S x| ≤ 1)
    (hsize : 2*t = 2^k) (hk : 100*r+12 ≤ k) (hθ : 0 < θ)
    (hcover : ∀ S : Submodule Binary (e → N → Binary),
      ∀ T : Submodule Binary (Module.Dual Binary (e → N → Binary)),
      Componentwise S → DualComponentwise T →
      (Module.finrank Binary S : ℝ) ≤ (r : ℝ)*(2*t) →
      (Module.finrank Binary T : ℝ) ≤ (r : ℝ)*(2*t) →
      cellMass μ (fun x => projection (LinearMap.piMap (fun i => (A x i).mulVecLin)) S T = 0) ≤ p) :
    cellMass (weights (Lax342547.RawLaw.uniformLaw E))
      (fun o => ∃ S : e → Matrix N N Binary, (∑ i, (S i).rank) ≤ r ∧
        θ ≤ |∑ x, μ x*ψ S x*tensorCharacter h (A x) (columnsEquiv h (fun a => channels (o a)))|) ≤
      (r+1 : ℝ)^Fintype.card e*(2 : ℝ)^(2*Fintype.card N*r)*
        (2 : ℝ)^(Fintype.card e*(h*h+2))*
        (((4 : ℝ)^(2*t)*p^(2^(k-(100*r+10)))+1/(2 : ℝ)^(h*2^(k-(100*r+12))))/θ^(2*t)) := by
  classical
  let C := {S : e → Matrix N N Binary // (∑ i, (S i).rank) ≤ r}
  have hh := Lax342547.UniformPhaseTails.no_cover_raw_family_tail (C := C) E μ A (fun c => ψ c.val)
    r h t k p θ hN hμ hp0 hp1 hr hA (fun c => hψ c.val c.property) hsize hk hθ hcover
  have hc : (Fintype.card C : ℝ) ≤ (r+1 : ℝ)^Fintype.card e*(2 : ℝ)^(2*Fintype.card N*r) := by
    have ht := Lax342547.TotalRankCount.total_rank_card (e := e) (I := N) (J := N) r
    have he : (Fintype.card N+Fintype.card N)*r = 2*Fintype.card N*r := by ring
    rw [he] at ht
    exact_mod_cast ht
  have he : (fun o : e → Frame B (Fin h) N E => ∃ c : C,
      θ ≤ |∑ x, μ x*ψ c.val x*tensorCharacter h (A x) (columnsEquiv h (fun a => channels (o a)))|) =
      (fun o => ∃ S : e → Matrix N N Binary, (∑ i, (S i).rank) ≤ r ∧
        θ ≤ |∑ x, μ x*ψ S x*tensorCharacter h (A x) (columnsEquiv h (fun a => channels (o a)))|) := by
    funext o
    apply propext
    constructor
    · rintro ⟨c,hc⟩
      exact ⟨c.val,c.property,hc⟩
    · rintro ⟨S,hS,hp⟩
      exact ⟨⟨S,hS⟩,hp⟩
  rw [he] at hh
  apply hh.trans
  have hb : 0 ≤ ((4 : ℝ)^(2*t)*p^(2^(k-(100*r+10)))+1/(2 : ℝ)^(h*2^(k-(100*r+12))))/θ^(2*t) := by positivity
  simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (by positivity)) hb

end Lax342547Proofs.UniformPhaseTails
