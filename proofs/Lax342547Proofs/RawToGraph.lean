import Lax342547.RawToGraph
import Lax342547Proofs.UnitContainers
import Lax342547Proofs.GoodSamples
import Lax342547Proofs.MatchingCoverage

namespace Lax342547Proofs.RawToGraph
open Lax342547.RawToGraph

set_option backward.isDefEq.respectTransparency false
open Lax342547.RelativeEntropy Lax342547.UnitLaws Lax342547.ContainerLaws
open Lax342547.RetainedImages Lax342547.CellAveraging Lax342547.FiniteSampling
open Lax342547.GoodSamples Lax342547.MatchingSamples Lax342547.SampledGraph Lax342547.ConnectedMatching

/--
---
conclusion: Lax342547.RawToGraph.exception_budget_nonneg
---
-/
theorem exception_budget_nonneg (m k : ℕ) (M κ : ℝ) (hM : 0 < M) (hκ : 0 < κ) :
    0 ≤ exceptionBudget m k M κ := by
  unfold exceptionBudget
  positivity

/--
---
conclusion: Lax342547.RawToGraph.supersaturation_to_sample
---
-/
theorem supersaturation_to_sample {Ω : Type} [Fintype Ω] [Nonempty Ω]
    (μ : Ω → ℝ) (hole : Ω → Ω → Prop)
    (hsymm : ∀ ⦃x y⦄, hole x y → hole y x) (hloop : ∀ x, ¬ hole x x)
    (htriangle : ∀ x y z, hole x y → hole y z → ¬ hole z x)
    (M κ ε : ℝ) (m k L : ℕ)
    (hμ : Probability μ) (hμpos : ∀ x, 0 < μ x)
    (hM : 0 < M) (hκ : 0 < κ) (hε : 0 < ε) (hε1 : ε < 1)
    (hL : Real.log κ/(-Real.log (1-ε))+1 ≤ L)
    (hscale : 200*(k-1) < m)
    (hbudget : (((Fintype.card Ω^2+1)^L : ℕ) : ℝ)*exceptionBudget m k M κ < 1)
    (hsuper : ∀ ρ, Feasible μ (fun x y => ¬ hole x y) M κ ρ →
      ε ≤ conflictMass ρ (fourConflict hole)) :
    ∃ sample : Fin m → Ω,
      (sampleGraph hole hsymm sample).indepNum ≤ 2 ∧
      100*connectedMatchingNumber (sampleGraph hole hsymm sample) < m := by
  classical
  obtain ⟨C,hcount,hterminal,hcover⟩ := Lax342547Proofs.UnitContainers.unit_container_family
    μ (fun x y => ¬ hole x y) (fourConflict hole) M κ ε L
    hμ hμpos hM hκ hε hε1 hL hsuper
  have hex : ∀ R : Finset (Ω × Ω), ∃ S : Ω → Prop, ∃ E : Ω → Ω → Prop,
      R ∈ C → cellMass μ S < 1/M ∧ pairEventMass μ μ E < 1/κ ∧
        (∀ x y, ¬ hole x y → (x,y) ∈ R → S x ∨ S y ∨ E x y) := by
    intro R
    by_cases hr : R ∈ C
    · obtain ⟨S,E,hS,hE,hcov⟩ := hterminal R hr
      exact ⟨S,E,fun _ => ⟨hS,hE,hcov⟩⟩
    · exact ⟨fun _ => False,fun _ _ => False,fun h => (hr h).elim⟩
  choose S E hcuts using hex
  have hCbudget : (C.card : ℝ)*exceptionBudget m k M κ < 1 := by
    have hc : (C.card : ℝ) ≤ ((Fintype.card Ω^2+1)^L : ℕ) := by exact_mod_cast hcount
    exact (mul_le_mul_of_nonneg_right hc (exception_budget_nonneg m k M κ hM hκ)).trans_lt hbudget
  obtain ⟨sample,hgood⟩ := Lax342547Proofs.GoodSamples.exists_good_sample μ C S E m k M κ hμ hM hκ
    (fun R hr => (hcuts R hr).1) (fun R hr => (hcuts R hr).2.1) hCbudget
  refine ⟨sample,Lax342547Proofs.SampledGraph.sampleGraph_indepNum_le_two hole hsymm htriangle sample,?_⟩
  apply Lax342547Proofs.MatchingCoverage.connected_matching_exception_bound hole hsymm sample k _ hscale
  intro matching hm
  let I := Finset.univ.image (fun e : matching => unitType sample e.val (hm.1 _ e.property).1)
  have hi := Lax342547Proofs.MatchingSamples.unit_types_independent hole hsymm hloop sample matching hm
  obtain ⟨R,hr,hIR⟩ := hcover I hi.2
  have hbad := hgood R hr
  have hS : (Finset.univ.filter (fun v => S R (sample v))).card < k := by
    apply Nat.lt_of_not_ge
    intro hh
    exact hbad (Or.inl hh)
  have hE : ¬ ∃ a : Fin k × Bool ↪ Fin m, ∀ j, E R (sample (a (j,false))) (sample (a (j,true))) := by
    intro hh
    exact hbad (Or.inr hh)
  apply Lax342547Proofs.MatchingCoverage.matching_exception_bound hole hsymm sample (S R) (E R)
    matching hm k _ hS hE
  intro e
  have he : unitType sample e.val (hm.1 _ e.property).1 ∈ I := Finset.mem_image.mpr ⟨e,Finset.mem_univ e,rfl⟩
  exact (hcuts R hr).2.2 _ _ (hi.1 _ he) (hIR he)

end Lax342547Proofs.RawToGraph
