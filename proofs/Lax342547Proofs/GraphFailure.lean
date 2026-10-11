import Lax342547.GraphFailure
import Lax342547.FiniteSampling
import Lax342547.GoodSamples
import Lax342547.MatchingCoverage
import Lax342547.MatchingSamples
import Lax342547.RawToGraph
import Lax342547.UnitContainers

namespace Lax342547Proofs.GraphFailure
open Lax342547.GraphFailure

set_option backward.isDefEq.respectTransparency false
open Lax342547.RelativeEntropy Lax342547.UnitLaws Lax342547.ContainerLaws
open Lax342547.RetainedImages Lax342547.CellAveraging Lax342547.FiniteSampling
open Lax342547.GoodSamples Lax342547.MatchingSamples Lax342547.SampledGraph Lax342547.ConnectedMatching
open Lax342547.RawToGraph
open scoped BigOperators

/--
---
conclusion: Lax342547.GraphFailure.graph_from_container_exceptions
---
-/
theorem graph_from_container_exceptions {Ω : Type}
    (hole : Ω → Ω → Prop) (hsymm : ∀ ⦃x y⦄, hole x y → hole y x) (hloop : ∀ x, ¬ hole x x)
    (C : Finset (Finset (Ω × Ω))) (S : Finset (Ω × Ω) → Ω → Prop)
    (E : Finset (Ω × Ω) → Ω → Ω → Prop)
    (hcover : ∀ I : Finset (Ω × Ω), (∀ x ∈ I, ∀ y ∈ I, ¬ fourConflict hole x y) → ∃ R ∈ C, I ⊆ R)
    (hcuts : ∀ R ∈ C, ∀ x y, ¬ hole x y → (x,y) ∈ R → S R x ∨ S R y ∨ E R x y)
    {m : ℕ} (sample : Fin m → Ω) (k : ℕ) (hscale : 200*(k-1) < m)
    (hgood : ∀ R ∈ C, ¬ Bad (S R) (E R) k sample) :
    100*connectedMatchingNumber (sampleGraph hole hsymm sample) < m := by
  classical
  apply Lax342547.MatchingCoverage.connected_matching_exception_bound hole hsymm sample k _ hscale
  intro matching hm
  let I := Finset.univ.image (fun e : matching => unitType sample e.val (hm.1 _ e.property).1)
  have hi := Lax342547.MatchingSamples.unit_types_independent hole hsymm hloop sample matching hm
  obtain ⟨R,hr,hIR⟩ := hcover I hi.2
  have hbad := hgood R hr
  have hS : (Finset.univ.filter (fun v => S R (sample v))).card < k := by
    apply Nat.lt_of_not_ge
    intro hh
    exact hbad (Or.inl hh)
  have hE : ¬ ∃ a : Fin k × Bool ↪ Fin m, ∀ j, E R (sample (a (j,false))) (sample (a (j,true))) := by
    intro hh
    exact hbad (Or.inr hh)
  apply Lax342547.MatchingCoverage.matching_exception_bound hole hsymm sample (S R) (E R)
    matching hm k _ hS hE
  intro e
  have he : unitType sample e.val (hm.1 _ e.property).1 ∈ I := Finset.mem_image.mpr ⟨e,Finset.mem_univ e,rfl⟩
  exact hcuts R hr _ _ (hi.1 _ he) (hIR he)

/--
---
conclusion: Lax342547.GraphFailure.sample_failure_bound
---
-/
theorem sample_failure_bound {Ω : Type} [Fintype Ω] [Nonempty Ω]
    (μ : Ω → ℝ) (hole : Ω → Ω → Prop)
    (hsymm : ∀ ⦃x y⦄, hole x y → hole y x) (hloop : ∀ x, ¬ hole x x)
    (M κ ε : ℝ) (m k L : ℕ)
    (hμ : Probability μ) (hμpos : ∀ x, 0 < μ x)
    (hM : 0 < M) (hκ : 0 < κ) (hε : 0 < ε) (hε1 : ε < 1)
    (hL : Real.log κ/(-Real.log (1-ε))+1 ≤ L)
    (hscale : 200*(k-1) < m)
    (hsuper : ∀ ρ, Feasible μ (fun x y => ¬ hole x y) M κ ρ →
      ε ≤ conflictMass ρ (fourConflict hole)) :
    cellMass (productLaw (fun _ : Fin m => μ))
      (fun sample => m ≤ 100*connectedMatchingNumber (sampleGraph hole hsymm sample)) ≤
        (((Fintype.card Ω^2+1)^L : ℕ) : ℝ)*exceptionBudget m k M κ := by
  classical
  obtain ⟨C,hcount,hterminal,hcover⟩ := Lax342547.UnitContainers.unit_container_family
    μ (fun x y => ¬ hole x y) (fourConflict hole) M κ ε L hμ hμpos hM hκ hε hε1 hL hsuper
  have hex : ∀ R : Finset (Ω × Ω), ∃ S : Ω → Prop, ∃ E : Ω → Ω → Prop,
      R ∈ C → cellMass μ S < 1/M ∧ pairEventMass μ μ E < 1/κ ∧
        (∀ x y, ¬ hole x y → (x,y) ∈ R → S x ∨ S y ∨ E x y) := by
    intro R
    by_cases hr : R ∈ C
    · obtain ⟨S,E,hS,hE,hcov⟩ := hterminal R hr
      exact ⟨S,E,fun _ => ⟨hS,hE,hcov⟩⟩
    · exact ⟨fun _ => False,fun _ _ => False,fun h => (hr h).elim⟩
  choose S E hcuts using hex
  have hprob := Lax342547.FiniteSampling.product_probability (fun _ : Fin m => μ) (fun _ => hμ)
  have hbad : ∀ sample : Fin m → Ω, m ≤ 100*connectedMatchingNumber (sampleGraph hole hsymm sample) →
      ∃ R ∈ C, Bad (S R) (E R) k sample := by
    intro sample hf
    by_contra hn
    push Not at hn
    have hh := Lax342547.GraphFailure.graph_from_container_exceptions hole hsymm hloop C S E hcover
      (fun R hr => (hcuts R hr).2.2) sample k hscale hn
    exact (not_lt_of_ge hf) hh
  calc
    _ ≤ cellMass (productLaw (fun _ : Fin m => μ)) (fun sample => ∃ R ∈ C, Bad (S R) (E R) k sample) :=
      Lax342547.FiniteSampling.cell_mass_mono _ _ _ hprob.1 hbad
    _ ≤ ∑ R ∈ C, cellMass (productLaw (fun _ : Fin m => μ)) (Bad (S R) (E R) k) :=
      Lax342547.FiniteSampling.cell_mass_union_bound _ _ C hprob.1
    _ ≤ ∑ R ∈ C, exceptionBudget m k M κ :=
      Finset.sum_le_sum (fun R hr => Lax342547.GoodSamples.bad_sample_bound
        μ (S R) (E R) m k M κ hμ hM hκ (hcuts R hr).1 (hcuts R hr).2.1)
    _ = (C.card : ℝ)*exceptionBudget m k M κ := by simp only [Finset.sum_const,nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcount)
      (Lax342547.RawToGraph.exception_budget_nonneg m k M κ hM hκ)

end Lax342547Proofs.GraphFailure
