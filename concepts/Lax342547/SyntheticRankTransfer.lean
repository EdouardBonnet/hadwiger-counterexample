import Lax342547.SmallSliceRank
import Lax342547.CommonTestTransfer

/-!
---
title: Quantitative common-test error obstruction for synthetic parity
type: lemma
---
On one common reference law, parity and all small coordinate-slice tests
are incompatible once the synthetic identity exceeds the sum of local ranks.
Separate empirical density caps and variance bounds transfer every test.
Their total prediction and comparison errors must then be at least one.
This is a conditional finite transfer theorem; constructing the actual
synthetic reference law and its empirical test couplings remains necessary.
-/

namespace Lax342547.SyntheticRankTransfer
noncomputable section
open Lax342547.MomentSpace Lax342547.SmallSliceRank Lax342547.RelativeEntropy
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

def indicator {Ω : Type} (C : Ω → Prop) (ω : Ω) : ℝ := by
  classical
  exact if C ω then 1 else 0

def eventMean {Ω : Type} [Fintype Ω] (μ : Ω → ℝ) (C : Ω → Prop) : ℝ :=
  ∑ ω,μ ω*indicator C ω

abbrev Points (m : ℕ) := Fin m → Binary

abbrev Tests (T : Type) (s m : ℕ) :=
  (Points m × Points m) ⊕ (T × (Fin (2*s+1) → Fin m) × (Fin (2*s+1) → Fin m))

def testCondition {T : Type} [Fintype T] (s m : ℕ)
    (F : T → Points m → Points m → Binary) : Tests T s m → Prop
  | Sum.inl (x,y) => (∑ l,F l x y) = dotProduct x y
  | Sum.inr (l,r,c) => Function.Injective r → Function.Injective c →
      HasProducts s (fun x y => F l (liftCoordinates r x) (liftCoordinates c y))

axiom incompatible_events {J Ω : Type} [Fintype J] [Fintype Ω]
    (μ : Ω → ℝ) (hμ : Probability μ) (C : J → Ω → Prop)
    (hincompatible : ∀ ω,¬∀ j,C j ω) : 1 ≤ ∑ j : J,(1-eventMean μ (C j))

axiom transferred_incompatible_events {J Ω : Type} [Fintype J] [Fintype Ω]
    (A : J → Type) [∀ j,Fintype (A j)]
    (μ : Ω → ℝ) (hμ : Probability μ) (C : J → Ω → Prop)
    (hincompatible : ∀ ω,¬∀ j,C j ω)
    (ρ σ F : ∀ j,A j → ℝ) (hσ : ∀ j,Probability (σ j))
    (L ε η : J → ℝ) (hL : ∀ j,0 ≤ L j)
    (hcap : ∀ j o,σ j o ≤ L j*ρ j o)
    (hvar : ∀ j,(∑ o,ρ j o*(F j o-eventMean μ (C j))^2) ≤ ε j)
    (hsuccess : ∀ j,1-η j ≤ ∑ o,σ j o*F j o) :
    1 ≤ ∑ j : J,(η j+Real.sqrt (L j*ε j))

axiom rank_tests_incompatible {T : Type} [Fintype T] (s m : ℕ)
    (F : T → Points m → Points m → Binary) (hm : 2*s*Fintype.card T < m) :
    ¬∀ j,testCondition s m F j

axiom prediction_error_budget {T Ω : Type} [Fintype T] [Fintype Ω]
    (s m : ℕ) (hm : 2*s*Fintype.card T < m)
    (μ : Ω → ℝ) (hμ : Probability μ)
    (pred : Ω → T → Points m → Points m → Binary)
    (A : Tests T s m → Type) [∀ j,Fintype (A j)]
    (ρ σ F : ∀ j,A j → ℝ) (hσ : ∀ j,Probability (σ j))
    (L ε η : Tests T s m → ℝ) (hL : ∀ j,0 ≤ L j)
    (hcap : ∀ j o,σ j o ≤ L j*ρ j o)
    (hvar : ∀ j,(∑ o,ρ j o*(F j o-eventMean μ (fun ω => testCondition s m (pred ω) j))^2) ≤ ε j)
    (hsuccess : ∀ j,1-η j ≤ ∑ o,σ j o*F j o) :
    1 ≤ ∑ j : Tests T s m,(η j+Real.sqrt (L j*ε j))

axiom uniform_prediction_error {T Ω : Type} [Fintype T] [Fintype Ω]
    (s m : ℕ) (hm : 2*s*Fintype.card T < m)
    (μ : Ω → ℝ) (hμ : Probability μ)
    (pred : Ω → T → Points m → Points m → Binary)
    (A : Tests T s m → Type) [∀ j,Fintype (A j)]
    (ρ σ F : ∀ j,A j → ℝ) (hσ : ∀ j,Probability (σ j))
    (L ε η : ℝ) (hL : 0 ≤ L)
    (hcap : ∀ j o,σ j o ≤ L*ρ j o)
    (hvar : ∀ j,(∑ o,ρ j o*(F j o-eventMean μ (fun ω => testCondition s m (pred ω) j))^2) ≤ ε)
    (hsuccess : ∀ j,1-η ≤ ∑ o,σ j o*F j o) :
    1 ≤ (Fintype.card (Tests T s m) : ℝ)*(η+Real.sqrt (L*ε))

axiom exists_error_margin (J : Type) [Fintype J] (L : ℝ) (hL : 0 ≤ L) :
    ∃ η : ℝ,0 < η ∧ ∃ ε : ℝ,0 < ε ∧
      (Fintype.card J : ℝ)*(η+Real.sqrt (L*ε)) < 1

end
end Lax342547.SyntheticRankTransfer
