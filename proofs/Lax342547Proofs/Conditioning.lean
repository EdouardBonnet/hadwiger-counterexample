import Lax342547.Conditioning

namespace Lax342547Proofs.Conditioning

open scoped ENNReal

theorem mass_ne_zero {Ω : Type} (p : PMF Ω) (S : Set Ω)
    (hS : ∃ o ∈ S, o ∈ p.support) : p.toOuterMeasure S ≠ 0 := by
  intro hz
  have hd := (p.toOuterMeasure_apply_eq_zero_iff S).mp hz
  obtain ⟨o, ho, hop⟩ := hS
  exact Set.disjoint_left.mp hd hop ho

theorem mass_ne_top {Ω : Type} (p : PMF Ω) (S : Set Ω) : p.toOuterMeasure S ≠ ⊤ := by
  rw [PMF.toOuterMeasure_apply]
  exact p.tsum_coe_indicator_ne_top S

theorem support_of_positive {Ω : Type} (p : PMF Ω) (S : Set Ω)
    (hS : 0 < p.toOuterMeasure S) : ∃ o ∈ S, o ∈ p.support := by
  by_contra hn
  have hd : Disjoint p.support S := Set.disjoint_left.mpr (fun o hop ho => hn ⟨o, ho, hop⟩)
  exact (ne_of_gt hS) ((p.toOuterMeasure_apply_eq_zero_iff S).mpr hd)

/--
---
conclusion: Lax342547.Conditioning.filter_event
---
Expand the finite event sum and factor out the common inverse retained
mass from the conditional point probabilities.
-/
theorem filter_event {Ω : Type} [Fintype Ω] (p : PMF Ω) (S T : Set Ω)
    (hS : ∃ o ∈ S, o ∈ p.support) :
    (p.filter S hS).toOuterMeasure T = p.toOuterMeasure (S ∩ T) / p.toOuterMeasure S := by
  classical
  rw [PMF.toOuterMeasure_apply_fintype, PMF.toOuterMeasure_apply_fintype p (S ∩ T),
    div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro o _
  by_cases ht : o ∈ T
  · rw [Set.indicator_of_mem ht, PMF.filter_apply, ← PMF.toOuterMeasure_apply]
    by_cases hs : o ∈ S <;> simp [hs, ht]
  · simp [ht]

/--
---
conclusion: Lax342547.Conditioning.filter_event_bound
---
A relative event bound before normalization divides by the positive,
finite retained mass to give precisely the corresponding probability cap.
-/
theorem filter_event_bound {Ω : Type} [Fintype Ω] (p : PMF Ω) (S T : Set Ω)
    (hS : ∃ o ∈ S, o ∈ p.support) (c : ℝ≥0∞)
    (hc : p.toOuterMeasure (S ∩ T) ≤ c * p.toOuterMeasure S) :
    (p.filter S hS).toOuterMeasure T ≤ c := by
  rw [Lax342547.Conditioning.filter_event]
  exact (ENNReal.div_le_iff (mass_ne_zero p S hS) (mass_ne_top p S)).mpr hc

/--
---
conclusion: Lax342547.Conditioning.filter_density
---
The conditional density costs exactly the inverse retained mass; outside
the conditioning set the conditional point mass is zero.
-/
theorem filter_density {Ω : Type} (p μ : PMF Ω) (S : Set Ω)
    (hS : ∃ o ∈ S, o ∈ p.support) (c : ℝ≥0∞) (hc : ∀ o, p o ≤ c * μ o) :
    ∀ o, (p.filter S hS) o ≤ (c / p.toOuterMeasure S) * μ o := by
  classical
  intro o
  rw [PMF.filter_apply, ← PMF.toOuterMeasure_apply, div_eq_mul_inv]
  by_cases ho : o ∈ S
  · rw [Set.indicator_of_mem ho]
    calc
      _ ≤ (c * μ o) * (p.toOuterMeasure S)⁻¹ := mul_le_mul_of_nonneg_right (hc o) zero_le
      _ = _ := by ac_rfl
  · simp [ho]

/--
---
conclusion: Lax342547.Conditioning.weighted_filter
---
Multiplying the conditional law by its actual retained mass cancels the
normalization and recovers the original restricted point mass exactly.
-/
theorem weighted_filter {Ω : Type} (p : PMF Ω) (S : Set Ω)
    (hS : ∃ o ∈ S, o ∈ p.support) (o : Ω) :
    p.toOuterMeasure S * (p.filter S hS) o = S.indicator p o := by
  rw [PMF.filter_apply, ← PMF.toOuterMeasure_apply]
  rw [mul_left_comm, ENNReal.mul_inv_cancel (mass_ne_zero p S hS) (mass_ne_top p S), mul_one]

/--
---
conclusion: Lax342547.Conditioning.disjoint_mixture
---
Each conditional part is weighted by its original mass. Disjointness
ensures that a retained point belongs to exactly one part, so the sum
recovers the unnormalized retained law pointwise.
-/
theorem disjoint_mixture {Ω J : Type} [DecidableEq Ω] (p : PMF Ω)
    (L : Finset J) (S : J → Finset Ω)
    (hdisjoint : ∀ i ∈ L, ∀ j ∈ L, i ≠ j → Disjoint (S i) (S j))
    (hS : ∀ j ∈ L, ∃ o ∈ (S j : Set Ω), o ∈ p.support) (o : Ω) :
    (∑ j : {j // j ∈ L}, p.toOuterMeasure (S j.val) * (p.filter (S j.val) (hS j.val j.property)) o) =
      (L.biUnion S : Set Ω).indicator p o := by
  classical
  simp only [Lax342547.Conditioning.weighted_filter]
  by_cases ho : o ∈ L.biUnion S
  · obtain ⟨j, hj, hoj⟩ := Finset.mem_biUnion.mp ho
    rw [Set.indicator_of_mem ho, Finset.sum_eq_single (⟨j, hj⟩ : {j // j ∈ L})]
    · exact Set.indicator_of_mem hoj p
    · intro i _ hij
      apply Set.indicator_of_notMem
      intro hoi
      have hi : i.val ≠ j := fun he => hij (Subtype.ext he)
      exact Finset.disjoint_left.mp (hdisjoint i.val i.property j hj hi) hoi hoj
    · simp
  · rw [Set.indicator_of_notMem ho]
    apply Finset.sum_eq_zero
    intro j _
    exact Set.indicator_of_notMem (fun hj => ho (Finset.mem_biUnion.mpr ⟨j.val, j.property, hj⟩)) p

end Lax342547Proofs.Conditioning
