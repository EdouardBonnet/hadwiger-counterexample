import Lax342547.AcceptingInjection
import Lax342547.AcceptingFamilies
import Lax342547.FiniteInjection
import Lax342547.GreedySpaces
import Lax342547.UnitSpanAvoidance

namespace Lax342547Proofs.AcceptingInjection
open Lax342547.AcceptingInjection

set_option backward.isDefEq.respectTransparency false
open Lax342547.MomentSpace Lax342547.RelativeEntropy Lax342547.RetainedImages
open Lax342547.RealCellLaws Lax342547.PushforwardWalsh Lax342547.FiniteInjection
open Lax342547.RawFrames
open scoped BigOperators

/--
---
conclusion: Lax342547.AcceptingInjection.accepting_family_injection
---
-/
theorem accepting_family_injection {A B I N H : Type}
    [Fintype A] [Fintype B] [Fintype I] [Fintype N] [Fintype H]
    [DecidableEq N] [DecidableEq H]
    (α : A → ℝ) (β : B → ℝ) (C : I → A → Prop) (key : B → I)
    (V : A → Submodule Binary (N → Binary)) (Y : B → Matrix N H Binary)
    (S : B → Submodule Binary (H → Binary)) (K ℓ : ℕ) (L η δ τ : ℝ)
    (hα : Probability α) (hβ : Probability β) (hL : 0 ≤ L) (hη : 0 ≤ η)
    (hτ : 0 < τ) (hgap : δ < η)
    (hV : ∀ a,Module.finrank Binary (V a) ≤ K)
    (hS : ∀ b,Module.finrank Binary (S b) ≤ K)
    (hcap : ∀ y,push β Y y ≤ L*weights (PMF.uniformOfFintype (Matrix N H Binary)) y)
    (havoid : ∀ i,τ ≤ cellMass α (C i) → ∀ j,j < ℓ → ∀ t : Fin j → A,
      cellMass (conditionalLaw α (C i)) (fun a => ¬ Disjoint (V a) (⨆ k : Fin j,V (t k))) ≤ δ) :
    (∑ b,β b*cellMass α (fun a => C (key b) a ∧ pinFailure (V a) (Y b) (S b))) ≤
      η*(∑ b,β b*cellMass α (C (key b))) + τ +
      Fintype.card I*((L*((2 : ℝ)^(Fintype.card H*K+2*K*ℓ)/(2 : ℝ)^(Fintype.card H*ℓ)))/(η-δ)^ℓ) := by
  apply Lax342547.AcceptingFamilies.accepting_family_loss α β C key
    (fun b a => pinFailure (V a) (Y b) (S b)) η τ _ hα hβ hη hτ (by positivity)
  intro i hi
  exact Lax342547.FiniteInjection.finite_injection_exception (conditionalLaw α (C i)) β V Y S
    K ℓ L η δ (Lax342547.AcceptingFamilies.conditional_probability α (C i) hα (lt_of_lt_of_le hτ hi))
    hβ hL hgap hV hS hcap (havoid i hi)

/--
---
conclusion: Lax342547.AcceptingInjection.primal_accepting_family_injection
---
-/
theorem primal_accepting_family_injection {A B I P N H : Type}
    [Fintype A] [Fintype B] [Fintype I] [Fintype P] [Fintype N] [Fintype H]
    [DecidableEq P] [DecidableEq N] [DecidableEq H]
    (E : Matrix P P Binary) [Nonempty (Frame P H N E)]
    (α : A → ℝ) (β : B → ℝ) (C : I → A → Prop) (key : B → I)
    (image : A → Frame P H N E) (V : A → Submodule Binary (N → Binary))
    (Y : B → Matrix N H Binary) (S : B → Submodule Binary (H → Binary))
    (K ℓ : ℕ) (M L η τ : ℝ)
    (hα : Probability α) (hβ : Probability β) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hη : 0 ≤ η) (hτ : 0 < τ)
    (hN : Fintype.card P+Fintype.card H+1 ≤ Fintype.card N)
    (hV : ∀ a,V a ≤ LinearMap.range (image a).P.mulVecLin)
    (hdV : ∀ a,Module.finrank Binary (V a) ≤ K)
    (hS : ∀ b,Module.finrank Binary (S b) ≤ K)
    (hAcap : ∀ f,push α image f ≤ M*weights (PMF.uniformOfFintype (Frame P H N E)) f)
    (hBcap : ∀ y,push β Y y ≤ L*weights (PMF.uniformOfFintype (Matrix N H Binary)) y)
    (hgap : (M/τ)*(2*((2 : ℝ)^(Fintype.card P+Fintype.card H+K*ℓ)/(2 : ℝ)^Fintype.card N)) < η) :
    (∑ b,β b*cellMass α (fun a => C (key b) a ∧ pinFailure (V a) (Y b) (S b))) ≤
      η*(∑ b,β b*cellMass α (C (key b))) + τ +
      Fintype.card I*((L*((2 : ℝ)^(Fintype.card H*K+2*K*ℓ)/(2 : ℝ)^(Fintype.card H*ℓ)))/
        (η-(M/τ)*(2*((2 : ℝ)^(Fintype.card P+Fintype.card H+K*ℓ)/(2 : ℝ)^Fintype.card N)))^ℓ) := by
  apply Lax342547.AcceptingInjection.accepting_family_injection α β C key V Y S K ℓ L η _ τ hα hβ hL hη hτ hgap hdV hS hBcap
  intro i hi j hj t
  have hdim := Lax342547.GreedySpaces.accumulated_dimension V K j t hdV
  have hd : Module.finrank Binary ↥(⨆ k : Fin j,V (t k)) ≤ K*ℓ :=
    hdim.trans (Nat.mul_le_mul_left K hj.le)
  have ha := Lax342547.UnitSpanAvoidance.conditioned_unit_span_avoidance E α image V
    (⨆ k : Fin j,V (t k)) (C i) M τ hα.1 hM hτ hi hN hV hAcap
  exact ha.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
        (Nat.add_le_add_left hd _)) (by positivity)) (by norm_num : (0 : ℝ) ≤ 2))
    (div_nonneg hM hτ.le))

end Lax342547Proofs.AcceptingInjection
