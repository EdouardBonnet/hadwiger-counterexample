import Lax342547.SyntheticRankTransfer
import Lax342547.CommonTestTransfer
import Lax342547.SmallSliceRank

namespace Lax342547Proofs.SyntheticRankTransfer
noncomputable section
open Lax342547.MomentSpace Lax342547.SmallSliceRank Lax342547.RelativeEntropy
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
open Lax342547.SyntheticRankTransfer

/--
---
conclusion: Lax342547.SyntheticRankTransfer.incompatible_events
---
-/
theorem incompatible_events {J Ω : Type} [Fintype J] [Fintype Ω]
    (μ : Ω → ℝ) (hμ : Probability μ) (C : J → Ω → Prop)
    (hincompatible : ∀ ω,¬∀ j,C j ω) : 1 ≤ ∑ j : J,(1-eventMean μ (C j)) := by
  classical
  have hp (ω : Ω) : 1 ≤ ∑ j,(1-indicator (C j) ω) := by
    obtain ⟨j,hj⟩ := not_forall.mp (hincompatible ω)
    calc
      1 = 1-indicator (C j) ω := by simp [indicator,hj]
      _ ≤ ∑ j,(1-indicator (C j) ω) :=
        Finset.single_le_sum (f := fun i => 1-indicator (C i) ω) (fun i _ => by unfold indicator; split_ifs <;> norm_num) (Finset.mem_univ j)
  calc
    1 = ∑ ω,μ ω := hμ.2.symm
    _ ≤ ∑ ω,μ ω*(∑ j,(1-indicator (C j) ω)) :=
      Finset.sum_le_sum (fun ω _ => by simpa only [mul_one] using mul_le_mul_of_nonneg_left (hp ω) (hμ.1 ω))
    _ = ∑ j : J,(1-eventMean μ (C j)) := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      simp only [mul_sub,mul_one,Finset.sum_sub_distrib,hμ.2,eventMean]

/--
---
conclusion: Lax342547.SyntheticRankTransfer.transferred_incompatible_events
---
-/
theorem transferred_incompatible_events {J Ω : Type} [Fintype J] [Fintype Ω]
    (A : J → Type) [∀ j,Fintype (A j)]
    (μ : Ω → ℝ) (hμ : Probability μ) (C : J → Ω → Prop)
    (hincompatible : ∀ ω,¬∀ j,C j ω)
    (ρ σ F : ∀ j,A j → ℝ) (hσ : ∀ j,Probability (σ j))
    (L ε η : J → ℝ) (hL : ∀ j,0 ≤ L j)
    (hcap : ∀ j o,σ j o ≤ L j*ρ j o)
    (hvar : ∀ j,(∑ o,ρ j o*(F j o-eventMean μ (C j))^2) ≤ ε j)
    (hsuccess : ∀ j,1-η j ≤ ∑ o,σ j o*F j o) :
    1 ≤ ∑ j : J,(η j+Real.sqrt (L j*ε j)) := by
  apply (Lax342547.SyntheticRankTransfer.incompatible_events μ hμ C hincompatible).trans
  apply Finset.sum_le_sum
  intro j _
  have hh := Lax342547.CommonTestTransfer.success_transfer (ρ j) (σ j) (F j) (hσ j)
    (L j) (ε j) (eventMean μ (C j)) (η j) (hL j) (hcap j) (hvar j) (hsuccess j)
  linarith

/--
---
conclusion: Lax342547.SyntheticRankTransfer.rank_tests_incompatible
---
-/
theorem rank_tests_incompatible {T : Type} [Fintype T] (s m : ℕ)
    (F : T → Points m → Points m → Binary) (hm : 2*s*Fintype.card T < m) :
    ¬∀ j,testCondition s m F j := by
  intro hh
  apply Lax342547.SmallSliceRank.parity_rank_contradiction s m F
  · intro x y
    exact hh (Sum.inl (x,y))
  · intro l r c hr hc
    exact hh (Sum.inr (l,r,c)) hr hc
  · exact hm

/--
---
conclusion: Lax342547.SyntheticRankTransfer.prediction_error_budget
---
-/
theorem prediction_error_budget {T Ω : Type} [Fintype T] [Fintype Ω]
    (s m : ℕ) (hm : 2*s*Fintype.card T < m)
    (μ : Ω → ℝ) (hμ : Probability μ)
    (pred : Ω → T → Points m → Points m → Binary)
    (A : Tests T s m → Type) [∀ j,Fintype (A j)]
    (ρ σ F : ∀ j,A j → ℝ) (hσ : ∀ j,Probability (σ j))
    (L ε η : Tests T s m → ℝ) (hL : ∀ j,0 ≤ L j)
    (hcap : ∀ j o,σ j o ≤ L j*ρ j o)
    (hvar : ∀ j,(∑ o,ρ j o*(F j o-eventMean μ (fun ω => testCondition s m (pred ω) j))^2) ≤ ε j)
    (hsuccess : ∀ j,1-η j ≤ ∑ o,σ j o*F j o) :
    1 ≤ ∑ j : Tests T s m,(η j+Real.sqrt (L j*ε j)) := by
  exact Lax342547.SyntheticRankTransfer.transferred_incompatible_events A μ hμ
    (fun j ω => testCondition s m (pred ω) j)
    (fun ω => Lax342547.SyntheticRankTransfer.rank_tests_incompatible s m (pred ω) hm)
    ρ σ F hσ L ε η hL hcap hvar hsuccess

/--
---
conclusion: Lax342547.SyntheticRankTransfer.uniform_prediction_error
---
-/
theorem uniform_prediction_error {T Ω : Type} [Fintype T] [Fintype Ω]
    (s m : ℕ) (hm : 2*s*Fintype.card T < m)
    (μ : Ω → ℝ) (hμ : Probability μ)
    (pred : Ω → T → Points m → Points m → Binary)
    (A : Tests T s m → Type) [∀ j,Fintype (A j)]
    (ρ σ F : ∀ j,A j → ℝ) (hσ : ∀ j,Probability (σ j))
    (L ε η : ℝ) (hL : 0 ≤ L)
    (hcap : ∀ j o,σ j o ≤ L*ρ j o)
    (hvar : ∀ j,(∑ o,ρ j o*(F j o-eventMean μ (fun ω => testCondition s m (pred ω) j))^2) ≤ ε)
    (hsuccess : ∀ j,1-η ≤ ∑ o,σ j o*F j o) :
    1 ≤ (Fintype.card (Tests T s m) : ℝ)*(η+Real.sqrt (L*ε)) := by
  have hh := Lax342547.SyntheticRankTransfer.prediction_error_budget s m hm μ hμ pred A ρ σ F hσ
    (fun _ => L) (fun _ => ε) (fun _ => η) (fun _ => hL) hcap hvar hsuccess
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using hh

/--
---
conclusion: Lax342547.SyntheticRankTransfer.exists_error_margin
---
-/
theorem exists_error_margin (J : Type) [Fintype J] (L : ℝ) (hL : 0 ≤ L) :
    ∃ η : ℝ,0 < η ∧ ∃ ε : ℝ,0 < ε ∧
      (Fintype.card J : ℝ)*(η+Real.sqrt (L*ε)) < 1 := by
  let c : ℝ := Fintype.card J
  have hc : 0 ≤ c := Nat.cast_nonneg _
  let η : ℝ := 1/(4*(c+1))
  have hη : 0 < η := by dsimp [η]; positivity
  let ε : ℝ := η^2/(L+1)
  have hε : 0 < ε := by dsimp [ε]; positivity
  refine ⟨η,hη,ε,hε,?_⟩
  have hs : Real.sqrt (L*ε) ≤ η := by
    apply (Real.sqrt_le_left hη.le).mpr
    dsimp [ε]
    rw [← mul_div_assoc,div_le_iff₀ (by positivity : 0 < L+1)]
    nlinarith [sq_nonneg η]
  have hsmall : c*(η+η) < 1 := by
    dsimp [η]
    field_simp
    nlinarith
  exact (mul_le_mul_of_nonneg_left (by linarith : η+Real.sqrt (L*ε) ≤ η+η) hc).trans_lt hsmall

end
end Lax342547Proofs.SyntheticRankTransfer
