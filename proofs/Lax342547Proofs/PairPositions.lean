import Lax342547.PairPositions
import Lax342547.CellAveraging
import Lax342547.DisjointSampling
import Lax342547.FiniteSampling

namespace Lax342547Proofs.PairPositions
open Lax342547.PairPositions

set_option backward.isDefEq.respectTransparency false
open Lax342547.RelativeEntropy Lax342547.RetainedImages Lax342547.FiniteSampling Lax342547.CellAveraging
open scoped BigOperators

/--
---
conclusion: Lax342547.PairPositions.distinct_pair_probability
---
-/
theorem distinct_pair_probability {ι Ω : Type} [Fintype ι] [Fintype Ω] [DecidableEq ι]
    (μ : Ω → ℝ) (E : Ω → Ω → Prop) (i j : ι) (hij : i ≠ j) (hμ : Probability μ) :
    cellMass (productLaw (fun _ : ι => μ)) (fun x => E (x i) (x j)) = pairEventMass μ μ E := by
  classical
  let a : Fin 1 × Bool ↪ ι := {
    toFun := fun z => if z.2 then j else i
    inj' := by
      rintro ⟨u,b⟩ ⟨v,c⟩ he
      have huv : u = v := Subsingleton.elim _ _
      subst v
      cases b <;> cases c <;> simp_all }
  have hh := Lax342547.DisjointSampling.disjoint_pair_probability μ a E hμ
  simpa [a] using hh

/--
---
conclusion: Lax342547.PairPositions.inevitable_pair_mass
---
-/
theorem inevitable_pair_mass {ι Ω : Type} [Fintype ι] [Fintype Ω] [DecidableEq ι]
    (μ : Ω → ℝ) (E : Ω → Ω → Prop) (hμ : Probability μ)
    (hevery : ∀ x : ι → Ω, ∃ i j, i ≠ j ∧ E (x i) (x j)) :
    1 ≤ (Fintype.card ι : ℝ)^2*pairEventMass μ μ E := by
  classical
  let ρ := productLaw (fun _ : ι => μ)
  have hprob := Lax342547.FiniteSampling.product_probability (fun _ : ι => μ) (fun _ => hμ)
  let B := fun ij : ι × ι => fun x : ι → Ω => ij.1 ≠ ij.2 ∧ E (x ij.1) (x ij.2)
  have hu := Lax342547.FiniteSampling.cell_mass_union_bound ρ B Finset.univ hprob.1
  have hm : cellMass ρ (fun x => ∃ ij ∈ (Finset.univ : Finset (ι × ι)), B ij x) = 1 := by
    unfold cellMass
    have hh : ∀ x : ι → Ω, ∃ ij ∈ (Finset.univ : Finset (ι × ι)), B ij x := by
      intro x
      obtain ⟨i,j,hij,hE⟩ := hevery x
      exact ⟨(i,j),Finset.mem_univ _,hij,hE⟩
    simp only [hh,ite_true]
    exact hprob.2
  rw [hm] at hu
  have hlocal (ij : ι × ι) : cellMass ρ (B ij) ≤ pairEventMass μ μ E := by
    by_cases hij : ij.1 = ij.2
    · have hm0 : cellMass ρ (B ij) = 0 := by simp [cellMass,B,hij]
      rw [hm0]
      exact Lax342547.CellAveraging.pair_event_mass_nonneg μ μ E hμ.1 hμ.1
    · simpa [B,ρ,hij] using (Lax342547.PairPositions.distinct_pair_probability μ E ij.1 ij.2 hij hμ).le
  exact hu.trans (by
    calc
      _ ≤ ∑ _ : ι × ι, pairEventMass μ μ E := Finset.sum_le_sum (fun ij _ => hlocal ij)
      _ = _ := by simp [Fintype.card_prod,pow_two,Nat.cast_mul])

end Lax342547Proofs.PairPositions
