import Lax342547.FiniteInjection
import Mathlib.LinearAlgebra.DFinsupp
import Lax342547.AmplifiedTests
import Lax342547.FiniteSampling
import Lax342547.IndependentSampling
import Lax342547.SequentialTests
import Lax342547.UniversalWitnesses

namespace Lax342547Proofs.FiniteInjection
open Lax342547.FiniteInjection

set_option backward.isDefEq.respectTransparency false
open Lax342547.MomentSpace Lax342547.RelativeEntropy Lax342547.RetainedImages Lax342547.FiniteSampling
open Lax342547.RealCellLaws Lax342547.PushforwardWalsh
open scoped BigOperators

/--
---
conclusion: Lax342547.FiniteInjection.finite_injection_exception
---
-/
theorem finite_injection_exception {A B N H : Type}
    [Fintype A] [Fintype B] [Fintype N] [Fintype H] [DecidableEq N] [DecidableEq H]
    (α : A → ℝ) (β : B → ℝ) (V : A → Submodule Binary (N → Binary))
    (Y : B → Matrix N H Binary) (S : B → Submodule Binary (H → Binary))
    (K ℓ : ℕ) (L η δ : ℝ) (hα : Probability α) (hβ : Probability β)
    (hL : 0 ≤ L) (hgap : δ < η) (hV : ∀ a,Module.finrank Binary (V a) ≤ K)
    (hS : ∀ b,Module.finrank Binary (S b) ≤ K)
    (hcap : ∀ y,push β Y y ≤ L*weights (PMF.uniformOfFintype (Matrix N H Binary)) y)
    (havoid : ∀ j,j < ℓ → ∀ t : Fin j → A,
      cellMass α (fun a => ¬ Disjoint (V a) (⨆ i : Fin j,V (t i))) ≤ δ) :
    cellMass β (fun b => η ≤ cellMass α (fun a => pinFailure (V a) (Y b) (S b))) ≤
      (L*((2 : ℝ)^(Fintype.card H*K+2*K*ℓ)/(2 : ℝ)^(Fintype.card H*ℓ)))/(η-δ)^ℓ := by
  classical
  let F := fun b a => pinFailure (V a) (Y b) (S b)
  let P := fun b => fun j (t : Fin j → A) a => F b a ∧ Disjoint (V a) (⨆ i : Fin j,V (t i))
  let T := fun t : Fin ℓ → A => fun b => Lax342547.SequentialTests.accepts (P b) ℓ t
  let bad := fun b => η ≤ cellMass α (F b)
  have hprob := Lax342547.FiniteSampling.product_probability (fun _ : Fin ℓ => α) (fun _ => hα)
  have hlow (b : B) (hb : bad b) : (η-δ)^ℓ ≤ cellMass (productLaw (fun _ : Fin ℓ => α)) (fun t => T t b) := by
    exact Lax342547.IndependentSampling.greedy_failure_lower_probability V α (F b) η δ ℓ hα hgap.le hb havoid
  have hu (t : Fin ℓ → A) : cellMass β (T t) ≤
      L*((2 : ℝ)^(Fintype.card H*K+2*K*ℓ)/(2 : ℝ)^(Fintype.card H*ℓ)) := by
    by_cases hi : iSupIndep (fun i => V (t i))
    · have hm : cellMass β (T t) ≤ cellMass β (fun b => ∀ i,pinFailure (V (t i)) (Y b) (S b)) := by
        apply Lax342547.FiniteSampling.cell_mass_mono _ _ _ hβ.1
        intro b hb
        exact Lax342547.SequentialTests.accepts_pointwise (P b) (F b) (fun _ _ _ h => h.1) ℓ t hb
      have hw := Lax342547.UniversalWitnesses.marked_unit_witness_probability (fun i => V (t i)) hi β Y S
        K L hβ.1 hL (fun i => hV (t i)) hS hcap
      exact hm.trans (by simpa only [Fintype.card_fin,pinFailure] using hw)
    · have hz : cellMass β (T t) = 0 := by
        unfold cellMass
        apply Finset.sum_eq_zero
        intro b _
        have hb : ¬ T t b := fun h => hi (Lax342547.IndependentSampling.accepted_spaces_independent V (F b) ℓ t h)
        exact if_neg hb
      rw [hz]
      positivity
  exact Lax342547.AmplifiedTests.amplified_bad_mass _ _ T bad ((η-δ)^ℓ) _ hprob hβ.1
    (pow_pos (sub_pos.mpr hgap) _) hlow hu

end Lax342547Proofs.FiniteInjection
