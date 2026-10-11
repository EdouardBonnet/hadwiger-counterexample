import Lax342547.SecondPeeling
import Lax342547.BoundedPeeling
import Lax342547.ExactPins
import Lax342547.MetadataPins
import Lax342547.MixtureRecovery
import Lax342547.SplitTrimming
import Lax342547Proofs.Conditioning

namespace Lax342547Proofs.SecondPeeling

open Lax342547.MomentSpace Lax342547.ExactPins Lax342547.MetadataPins
open Lax342547.LeafPartition Lax342547.BoundedPeeling Lax342547.SecondPeeling
open scoped ENNReal

/--
---
conclusion: Lax342547.SecondPeeling.final_rank_budget
---
The ceiling of the new-rank allowance costs less than one extra dimension.
For zeta at most one, the paper's final budget absorbs this and all old
and deliberately added pins, with uniform slack.
-/
theorem final_rank_budget (D ζ : ℝ) (K₁ u : ℕ)
    (hD : 0 ≤ D) (hζ : 0 < ζ) (hζ₁ : ζ ≤ 1) :
    K₁ + u + newBudget D ζ K₁ u ≤ finalBudget D ζ K₁ u := by
  have hk : (0 : ℝ) ≤ K₁ := by positivity
  have hu : (0 : ℝ) ≤ u := by positivity
  have hc : (newBudget D ζ K₁ u : ℝ) < 4 * (D + K₁ + u + 6) / ζ + 1 := by
    unfold newBudget
    rw [show startCost D K₁ u + 1 = D + K₁ + u + 6 by unfold startCost; ring]
    exact Nat.ceil_lt_add_one (show 0 ≤ 4 * (D + K₁ + u + 6) / ζ by positivity)
  have hlarge : (K₁ : ℝ) + u + (4 * (D + K₁ + u + 6) / ζ + 1) ≤
      10 * (D + K₁ + u + 10) / ζ := by
    apply (le_div_iff₀ hζ).mpr
    have hm : ((K₁ : ℝ) + u + 1) * ζ ≤ (K₁ : ℝ) + u + 1 := by
      exact (mul_le_mul_of_nonneg_left hζ₁ (by positivity)).trans_eq (mul_one _)
    have hcancel : (4 * (D + K₁ + u + 6) / ζ) * ζ = 4 * (D + K₁ + u + 6) :=
      div_mul_cancel₀ _ hζ.ne'
    nlinarith
  have hfinal : 10 * (D + K₁ + u + 10) / ζ ≤ (finalBudget D ζ K₁ u : ℝ) :=
    Nat.le_ceil _
  have hsum : (K₁ : ℝ) + u + newBudget D ζ K₁ u ≤ (finalBudget D ζ K₁ u : ℝ) := by
    linarith
  exact_mod_cast hsum

theorem supportFinset_coe {Ω : Type} [Fintype Ω] (p : PMF Ω) :
    (supportFinset p : Set Ω) = p.support := by
  classical
  ext o
  simp [supportFinset]

/--
---
conclusion: Lax342547.SecondPeeling.second_part
---
A retained record has positive mass, so choose a consistent point to join
its image pins to the old pins. The normalized fiber has the absolute D'
density bound. Apply bounded peeling on its full support, count only new
quotient dimensions, and charge them to the final total budget.
-/
theorem second_part {Ω J Axis I N : Type}
    [Fintype Ω] [DecidableEq Ω] [Fintype Axis] [Fintype I] [Fintype N]
    (p μ : PMF Ω) (A : Ω → Axis → (I → Binary) →ₗ[Binary] (N → Binary))
    (P₀ : Pin Axis I N) (S : Set Ω) (hS : ∃ o ∈ S, o ∈ p.support)
    (choice : Ω → J) (U : J → Axis → Submodule Binary (I → Binary))
    (D ζ ε : ℝ) (K₁ u : ℕ)
    (hD : 0 ≤ D) (hζ : 0 < ζ) (hζ₁ : ζ ≤ 1) (hε : ε ≤ ζ / 4)
    (hN : 0 < Fintype.card N) (hP : p.support ⊆ P₀.event A) (hPbudget : P₀.rank ≤ K₁)
    (hu : ∀ j, ∑ a, Module.finrank Binary (U j a) ≤ u)
    (hSbound : (2 : ℝ≥0∞) ^ (-(ζ * Fintype.card N)) ≤ p.toOuterMeasure S)
    (hp : ∀ o, p o ≤ (2 : ℝ≥0∞) ^ ((D + K₁ + 1) * Fintype.card N) * μ o)
    (hreference : ∀ P : Pin Axis I N, μ.toOuterMeasure (P.event A) ≤
      (2 : ℝ≥0∞) ^ (-((1 - ε) * P.rank * Fintype.card N)))
    (k : Key N U)
    (hk : (2 : ℝ≥0∞) ^ (-(((u : ℝ) + 1) * Fintype.card N)) ≤
      (p.filter S hS).toOuterMeasure {o | record A choice U o = k}) :
    RepeeledPart (p.filter S hS) μ A P₀ choice U D ζ K₁ u k := by
  classical
  let q := p.filter S hS
  let T : Set Ω := {o | record A choice U o = k}
  have hpos : 0 < q.toOuterMeasure T :=
    (ENNReal.rpow_pos (by norm_num) (by norm_num)).trans_le hk
  have hkSupport := Conditioning.support_of_positive q T hpos
  refine ⟨hkSupport, ?_⟩
  let Q := q.filter T hkSupport
  let o := hkSupport.choose
  have hoT : o ∈ T := hkSupport.choose_spec.1
  have hoq : o ∈ q.support := hkSupport.choose_spec.2
  have hq : q.support ⊆ P₀.event A := by
    intro x hx
    exact hP ((PMF.mem_support_filter_iff hS).mp hx).2
  obtain ⟨P, hP₀, hPk, hdim, hwhole⟩ :=
    Lax342547.MetadataPins.refined_fiber A choice U u hu P₀ q.support hq o hoq
  have hkey : record A choice U o = k := hoT
  rw [hkey] at hPk hwhole
  have hinit : P.rank ≤ K₁ + u := hdim.trans (Nat.add_le_add_right hPbudget u)
  have hQP : Q.support ⊆ P.event A := by
    intro x hx
    have hx' := (PMF.mem_support_filter_iff hkSupport).mp hx
    exact hwhole ⟨hx'.2, hx'.1⟩
  have hdensity : ∀ x, Q x ≤ (2 : ℝ≥0∞) ^ (startCost D K₁ u * Fintype.card N) * μ x :=
    Lax342547.SplitTrimming.repinning_density p μ S T hS hkSupport D ζ (Fintype.card N) K₁ u
      hζ₁ hSbound hk hp
  obtain ⟨L, hL, hbounds⟩ := Lax342547.BoundedPeeling.bounded_partition Q μ A P (supportFinset Q)
    (by rw [supportFinset_coe]; exact hQP) (startCost D K₁ u) ζ ε (Fintype.card N)
    (newBudget D ζ K₁ u) hN hζ hζ₁ hε (Nat.le_ceil _) hdensity hreference
  have hresSubset : ((supportFinset Q : Set Ω) \ (L.biUnion Prod.fst : Set Ω)) ⊆ T := by
    intro x hx
    have hxQ : x ∈ Q.support := by
      rw [← supportFinset_coe]
      exact hx.1
    exact ((PMF.mem_support_filter_iff hkSupport).mp hxQ).1
  have hres := Lax342547.MixtureRecovery.conditional_event_mass q T
    (supportFinset Q \ L.biUnion Prod.fst) hkSupport hresSubset _
    (by simpa only [Finset.coe_sdiff] using hL.2.2)
  refine ⟨P, L, hP₀, hPk, hinit, hL, hres, fun z hz => ?_⟩
  obtain ⟨hzdim, hzlaw⟩ := hbounds z hz
  have hmono : P.rank ≤ z.2.rank := Lax342547.ExactPins.rank_mono P z.2 (hL.1 z hz).2.1
  have hbudget := Lax342547.SecondPeeling.final_rank_budget D ζ K₁ u hD hζ hζ₁
  exact ⟨by omega, hzlaw⟩

end Lax342547Proofs.SecondPeeling
