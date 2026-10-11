import Lax342547.RawAcceptingInjection
import Lax342547.AcceptingInjection
import Lax342547.ChannelColumns
import Lax342547.InjectionBudgets
import Lax342547.InjectiveDensity
import Lax342547.PhaseAverages

namespace Lax342547Proofs.RawAcceptingInjection
open Lax342547.RawAcceptingInjection

set_option backward.isDefEq.respectTransparency false
open Lax342547.MomentSpace Lax342547.RelativeEntropy Lax342547.RetainedImages
open Lax342547.RealCellLaws Lax342547.PushforwardWalsh Lax342547.FiniteInjection
open Lax342547.RawFrames Lax342547.FrameSymmetry
open scoped BigOperators

/--
---
conclusion: Lax342547.RawAcceptingInjection.capped_frame_channel
---
-/
theorem capped_frame_channel {B P N H : Type} [Fintype B] [Fintype P] [Fintype N] [Fintype H]
    [DecidableEq N] [DecidableEq H] (E : Matrix P P Binary) [Nonempty (Frame P H N E)]
    (β : B → ℝ) (image : B → Frame P H N E) (channel : Frame P H N E → Matrix N H Binary)
    (M : ℝ) (hM : 0 ≤ M)
    (hcap : ∀ f,push β image f ≤ M*weights (PMF.uniformOfFintype (Frame P H N E)) f)
    (hraw : ∀ y,push (weights (PMF.uniformOfFintype (Frame P H N E))) channel y ≤
      2*weights (PMF.uniformOfFintype (Matrix N H Binary)) y) :
    ∀ y,push β (fun b => channel (image b)) y ≤
      (2*M)*weights (PMF.uniformOfFintype (Matrix N H Binary)) y := by
  intro y
  have he := Lax342547.ChannelColumns.push_cell_mass β image (fun f => channel f = y)
  have hh := Lax342547.PhaseAverages.finite_event_density
    (weights (PMF.uniformOfFintype (Frame P H N E))) (push β image) M hcap (fun f => channel f = y)
  change cellMass β (fun b => channel (image b) = y) ≤ _
  rw [← he]
  have hr := mul_le_mul_of_nonneg_left (hraw y) hM
  change M*cellMass (weights (PMF.uniformOfFintype (Frame P H N E))) (fun f => channel f = y) ≤ _ at hr
  exact hh.trans (hr.trans_eq (by ring))

/--
---
conclusion: Lax342547.RawAcceptingInjection.raw_minus_accepting_injection
---
-/
theorem raw_minus_accepting_injection {A B I P N H : Type}
    [Fintype A] [Fintype B] [Fintype I] [Fintype P] [Fintype N] [Fintype H]
    [DecidableEq P] [DecidableEq N] [DecidableEq H]
    (E : Matrix P P Binary) [Nonempty (Frame P H N E)]
    (α : A → ℝ) (β : B → ℝ) (C : I → A → Prop) (key : B → I)
    (imageA : A → Frame P H N E) (imageB : B → Frame P H N E)
    (V : A → Submodule Binary (N → Binary)) (S : B → Submodule Binary (H → Binary))
    (K ℓ : ℕ) (M MB η τ : ℝ)
    (hα : Probability α) (hβ : Probability β) (hM : 0 ≤ M) (hMB : 0 ≤ MB)
    (hη : 0 ≤ η) (hτ : 0 < τ)
    (hN : Fintype.card P+Fintype.card H+1 ≤ Fintype.card N)
    (hV : ∀ a,V a ≤ LinearMap.range (imageA a).P.mulVecLin)
    (hdV : ∀ a,Module.finrank Binary (V a) ≤ K)
    (hS : ∀ b,Module.finrank Binary (S b) ≤ K)
    (hAcap : ∀ f,push α imageA f ≤ M*weights (PMF.uniformOfFintype (Frame P H N E)) f)
    (hBcap : ∀ f,push β imageB f ≤ MB*weights (PMF.uniformOfFintype (Frame P H N E)) f)
    (hgap : (M/τ)*(2*((2 : ℝ)^(Fintype.card P+Fintype.card H+K*ℓ)/(2 : ℝ)^Fintype.card N)) < η) :
    (∑ b,β b*cellMass α (fun a => C (key b) a ∧ pinFailure (V a) (imageB b).Y (S b))) ≤
      η*(∑ b,β b*cellMass α (C (key b))) + τ +
      Fintype.card I*(((2*MB)*((2 : ℝ)^(Fintype.card H*K+2*K*ℓ)/(2 : ℝ)^(Fintype.card H*ℓ)))/
        (η-(M/τ)*(2*((2 : ℝ)^(Fintype.card P+Fintype.card H+K*ℓ)/(2 : ℝ)^Fintype.card N)))^ℓ) := by
  let f : Frame P H N E := Classical.choice inferInstance
  letI : Nonempty (Injection H N) := ⟨minusChannel f⟩
  have hy := Lax342547.RawAcceptingInjection.capped_frame_channel E β imageB (fun f => f.Y) MB hMB hBcap
    (Lax342547.InjectiveDensity.raw_minus_channel_point_cap E (by omega))
  exact Lax342547.AcceptingInjection.primal_accepting_family_injection E α β C key imageA V
    (fun b => (imageB b).Y) S K ℓ M (2*MB) η τ hα hβ hM (by positivity) hη hτ
    hN hV hdV hS hAcap hy hgap

/--
---
conclusion: Lax342547.RawAcceptingInjection.exponential_accepting_injection
---
-/
theorem exponential_accepting_injection {A B I P N H : Type}
    [Fintype A] [Fintype B] [Fintype I] [Fintype P] [Fintype N] [Fintype H]
    [DecidableEq P] [DecidableEq N] [DecidableEq H]
    (E : Matrix P P Binary) [Nonempty (Frame P H N E)]
    (α : A → ℝ) (β : B → ℝ) (C : I → A → Prop) (key : B → I)
    (imageA : A → Frame P H N E) (imageB : B → Frame P H N E)
    (V : A → Submodule Binary (N → Binary)) (S : B → Submodule Binary (H → Binary))
    (K m t Cs : ℕ) (M MB η : ℝ)
    (hα : Probability α) (hβ : Probability β) (hM : 0 ≤ M) (hMB : 0 ≤ MB)
    (hη : 0 ≤ η) (hηt : 1/(2 : ℝ)^t ≤ η/2)
    (hN : Fintype.card P+Fintype.card H+1 ≤ Fintype.card N)
    (hb : Fintype.card P ≤ Fintype.card N/8)
    (hm : m+Fintype.card H+1 ≤ Fintype.card N/10)
    (hMcap : M ≤ (2 : ℝ)^m) (hMBcap : 2*MB ≤ (2 : ℝ)^(m+Fintype.card N))
    (hcount : (Fintype.card I : ℝ) ≤ (2 : ℝ)^(Cs*Fintype.card N))
    (hearly : 2*K+t+20*(K+1)*(Cs+3) ≤ Fintype.card H)
    (hlength : 20*(K+1) ≤ Fintype.card N)
    (hconstant : m+Fintype.card H*K ≤ Fintype.card N)
    (hsmall : 1/(2 : ℝ)^(Fintype.card N/2) ≤ η/2)
    (hV : ∀ a,V a ≤ LinearMap.range (imageA a).P.mulVecLin)
    (hdV : ∀ a,Module.finrank Binary (V a) ≤ K)
    (hS : ∀ b,Module.finrank Binary (S b) ≤ K)
    (hAcap : ∀ f,push α imageA f ≤ M*weights (PMF.uniformOfFintype (Frame P H N E)) f)
    (hBcap : ∀ f,push β imageB f ≤ MB*weights (PMF.uniformOfFintype (Frame P H N E)) f) :
    (∑ b,β b*cellMass α (fun a => C (key b) a ∧ pinFailure (V a) (imageB b).Y (S b))) ≤
      η*(∑ b,β b*cellMass α (C (key b))) + 1/(2 : ℝ)^(Fintype.card N/100) + 1/(2 : ℝ)^Fintype.card N := by
  let ℓ := Fintype.card N/(10*(K+1))
  let τ := 1/(2 : ℝ)^(Fintype.card N/100)
  let δ := (M/τ)*(2*((2 : ℝ)^(Fintype.card P+Fintype.card H+K*ℓ)/(2 : ℝ)^Fintype.card N))
  have hd : δ ≤ η/2 := (Lax342547.InjectionBudgets.conditioned_avoidance_budget K
    (Fintype.card P) (Fintype.card H) m (Fintype.card N) M hM hMcap hb hm).trans hsmall
  have hp : 0 < η/2 := lt_of_lt_of_le (by positivity) hηt
  have hgap : δ < η := by linarith
  have hgapdy : 1/(2 : ℝ)^t ≤ η-δ := by linarith
  have hf := Lax342547.RawAcceptingInjection.raw_minus_accepting_injection E α β C key imageA imageB V S K ℓ M MB η τ
    hα hβ hM hMB hη (by positivity) hN hV hdV hS hAcap hBcap hgap
  have hu := Lax342547.InjectionBudgets.accepting_family_exponential_budget K t Cs m
    (Fintype.card H) (Fintype.card N) (2*MB) (η-δ) (Fintype.card I)
    (by positivity) (by positivity) hgapdy hMBcap hcount hearly hlength hconstant
  exact hf.trans (add_le_add_right hu _)

end Lax342547Proofs.RawAcceptingInjection
