import Lax342547.TerminalCuts
import Lax342547.BipartiteFlows
import Lax342547.CellAveraging
import Lax342547.FlowCuts

namespace Lax342547Proofs.TerminalCuts
open Lax342547.TerminalCuts

set_option backward.isDefEq.respectTransparency false
open Lax342547.BipartiteFlows Lax342547.FlowCuts Lax342547.RetainedImages Lax342547.CellAveraging
open scoped BigOperators

/--
---
conclusion: Lax342547.TerminalCuts.law_iff_masked
---
-/
theorem law_iff_masked {Ω : Type} [Fintype Ω]
    (μ : Ω → ℝ) (R : Ω → Ω → Prop) (M κ : ℝ) (ρ : Ω → Ω → ℝ)
    (hμ : ∀ x, 0 ≤ μ x) (hκ : 0 ≤ κ) :
    Law (fun x => M*μ x) (fun y => M*μ y) (pairCapacity μ R κ) ρ ↔
      Lax342547.UnitLaws.Feasible μ R M κ (fun xy => ρ xy.1 xy.2) := by
  classical
  constructor
  · rintro ⟨hn,ht,hl,hr,hp⟩
    refine ⟨⟨fun xy => hn xy.1 xy.2,?_⟩,hl,hr,?_,?_⟩
    · simpa only [Fintype.sum_prod_type] using ht
    · intro xy
      have h := hp xy.1 xy.2
      by_cases hR : R xy.1 xy.2
      · simpa [pairCapacity,hR] using h
      · have hz : ρ xy.1 xy.2 = 0 := le_antisymm (by simpa [pairCapacity,hR] using h) (hn xy.1 xy.2)
        change ρ xy.1 xy.2 ≤ _
        rw [hz]
        exact mul_nonneg hκ (mul_nonneg (hμ xy.1) (hμ xy.2))
    · intro xy hR
      have h := hp xy.1 xy.2
      exact le_antisymm (by simpa [pairCapacity,hR] using h) (hn xy.1 xy.2)
  · rintro ⟨hprob,hl,hr,hp,hs⟩
    refine ⟨fun x y => hprob.1 (x,y),?_,hl,hr,?_⟩
    · simpa only [Fintype.sum_prod_type] using hprob.2
    · intro x y
      by_cases hR : R x y
      · simpa [pairCapacity,hR] using hp (x,y)
      · simp [pairCapacity,hR,hs (x,y) hR]

/--
---
conclusion: Lax342547.TerminalCuts.bipartite_cut_capacity
---
-/
theorem bipartite_cut_capacity {A B : Type} [Fintype A] [Fintype B]
    (a : A → ℝ) (b : B → ℝ) (p : A → B → ℝ) (Z : Finset (Vertex A B))
    (hs : source ∈ Z) (ht : sink ∉ Z) : by
      classical
      exact cutCapacity (capacity a b p) Z =
        (∑ x, if left x ∉ Z then a x else 0)+(∑ y, if right y ∈ Z then b y else 0)+
        (∑ x, ∑ y, if left x ∈ Z ∧ right y ∉ Z then p x y else 0) := by
  classical
  rw [Lax342547.FlowCuts.cut_indicator]
  simp only [Fintype.sum_sum_type,Fintype.sum_bool]
  change Sum.inl false ∈ Z at hs
  change Sum.inl true ∉ Z at ht
  simp [capacity,left,right,hs,ht,ite_and,Finset.sum_ite_irrel]
  ring


/--
---
conclusion: Lax342547.TerminalCuts.terminal_cut
---
-/
theorem terminal_cut {Ω : Type} [Fintype Ω]
    (μ : Ω → ℝ) (R : Ω → Ω → Prop) (M κ : ℝ)
    (hμ : ∀ x, 0 ≤ μ x) (hM : 0 < M) (hκ : 0 < κ)
    (hn : ¬ ∃ ρ, Lax342547.UnitLaws.Feasible μ R M κ ρ) :
    ∃ S : Ω → Prop, ∃ E : Ω → Ω → Prop,
      cellMass μ S < 1/M ∧ pairEventMass μ μ E < 1/κ ∧
      (∀ x y, R x y → S x ∨ S y ∨ E x y) := by
  classical
  have hpair : ∀ x y, 0 ≤ pairCapacity μ R κ x y := by
    intro x y
    unfold pairCapacity
    split_ifs
    · exact mul_nonneg hκ.le (mul_nonneg (hμ x) (hμ y))
    · exact le_rfl
  have hn' : ¬ ∃ ρ, Law (fun x => M*μ x) (fun y => M*μ y) (pairCapacity μ R κ) ρ := by
    rintro ⟨ρ,hρ⟩
    exact hn ⟨fun xy => ρ xy.1 xy.2, (Lax342547.TerminalCuts.law_iff_masked μ R M κ ρ hμ hκ.le).mp hρ⟩
  obtain ⟨Z,hs,ht,hcut⟩ := Lax342547.BipartiteFlows.infeasible_cut
    (fun x => M*μ x) (fun y => M*μ y) (pairCapacity μ R κ)
    (fun x => mul_nonneg hM.le (hμ x)) (fun y => mul_nonneg hM.le (hμ y)) hpair hn'
  let L : Ω → Prop := fun x => left x ∉ Z
  let T : Ω → Prop := fun y => right y ∈ Z
  let S : Ω → Prop := fun x => L x ∨ T x
  let E : Ω → Ω → Prop := fun x y => R x y ∧ left x ∈ Z ∧ right y ∉ Z
  have heq : cutCapacity (capacity (fun x => M*μ x) (fun y => M*μ y) (pairCapacity μ R κ)) Z =
      M*cellMass μ L+M*cellMass μ T+κ*pairEventMass μ μ E := by
    rw [Lax342547.TerminalCuts.bipartite_cut_capacity _ _ _ Z hs ht]
    unfold cellMass pairEventMass
    simp only [Finset.mul_sum]
    apply congrArg₂ (· + ·)
    · apply congrArg₂ (· + ·)
      · apply Finset.sum_congr rfl
        intro x _
        simp [L,mul_ite]
      · apply Finset.sum_congr rfl
        intro y _
        simp [T,mul_ite]
    · apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      simp only [pairCapacity,E,mul_ite,mul_zero]
      by_cases hR : R x y <;> by_cases hl : left x ∈ Z <;> by_cases hr : right y ∈ Z <;>
        simp [hR,hl,hr]
  rw [heq] at hcut
  have hL : 0 ≤ cellMass μ L := by
    unfold cellMass
    exact Finset.sum_nonneg (fun x _ => by split_ifs; exact hμ x; exact le_rfl)
  have hT : 0 ≤ cellMass μ T := by
    unfold cellMass
    exact Finset.sum_nonneg (fun x _ => by split_ifs; exact hμ x; exact le_rfl)
  have hE : 0 ≤ pairEventMass μ μ E :=
    Lax342547.CellAveraging.pair_event_mass_nonneg μ μ E hμ hμ
  have hS : cellMass μ S ≤ cellMass μ L+cellMass μ T := by
    unfold cellMass
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro x _
    by_cases hl : L x <;> by_cases ht : T x <;> simp [S,hl,ht,hμ x]
  refine ⟨S,E,?_,?_,?_⟩
  · apply (lt_div_iff₀ hM).mpr
    have hsM := mul_le_mul_of_nonneg_left hS hM.le
    nlinarith [mul_nonneg hκ.le hE]
  · apply (lt_div_iff₀ hκ).mpr
    nlinarith [mul_nonneg hM.le hL, mul_nonneg hM.le hT]
  · intro x y hR
    by_cases hx : S x
    · exact Or.inl hx
    by_cases hy : S y
    · exact Or.inr (Or.inl hy)
    right; right
    have hl : left x ∈ Z := by
      by_contra hh
      exact hx (Or.inl hh)
    have hr : right y ∉ Z := by
      intro hh
      exact hy (Or.inr hh)
    exact ⟨hR,hl,hr⟩

end Lax342547Proofs.TerminalCuts

