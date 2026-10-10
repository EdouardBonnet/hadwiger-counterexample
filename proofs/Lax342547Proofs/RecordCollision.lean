import Lax342547.RecordCollision
import Lax342547Proofs.KeyMeasures
import Lax342547Proofs.CellAveraging
import Lax342547Proofs.CollisionPruning

namespace Lax342547Proofs.RecordCollision
open Lax342547.RecordCollision

set_option backward.isDefEq.respectTransparency false
open Lax342547.KeyMeasures Lax342547.CellAveraging Lax342547.RetainedImages Lax342547.CollisionPruning

/--
---
conclusion: Lax342547.RecordCollision.key_record_mass_total
---
-/
theorem key_record_mass_total {Ω Q C : Type} [Fintype Ω] [Fintype C]
    (ρ : Ω → ℝ) (key : Ω → Q) (record : Ω → C) (accept : Ω → Prop) (q : Q) :
    (∑ c, keyRecordMass ρ key record accept q c) = keyMass ρ key accept q := by
  classical
  unfold keyRecordMass recordMass cellMass keyMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases ha : accept ω <;> by_cases hk : key ω = q <;>
    simp_all [Prod.mk.injEq, eq_comm]

/--
---
conclusion: Lax342547.RecordCollision.retained_key_record_identity
---
-/
theorem retained_key_record_identity {Q C D : Type} [Fintype Q] [Fintype C] [Fintype D]
    (a : Q → C → ℝ) (b : Q → D → ℝ) (τ : ℝ) :
    retainedPairs (fun qc : Q × C => a qc.1 qc.2) (fun qd : Q × D => b qd.1 qd.2)
      (fun qc qd => qc.1 = qd.1) τ = ∑ q, retained (a q) τ * retained (b q) τ := by
  classical
  unfold retainedPairs
  simp only [Fintype.sum_prod_type]
  have hi (q : Q) (c : C) :
      (∑ q', ∑ d, if q = q' ∧ τ ≤ a q c ∧ τ ≤ b q' d then a q c * b q' d else 0) =
      ∑ d, if τ ≤ a q c ∧ τ ≤ b q d then a q c * b q d else 0 := by
    have he (q' : Q) :
        (∑ d, if q = q' ∧ τ ≤ a q c ∧ τ ≤ b q' d then a q c * b q' d else 0) =
        if q = q' then (∑ d, if τ ≤ a q c ∧ τ ≤ b q d then a q c * b q d else 0) else 0 := by
      by_cases h : q = q'
      · subst q'; simp
      · simp [h]
    simp_rw [he]
    simp
  simp_rw [hi]
  apply Finset.sum_congr rfl
  intro q _
  unfold retained
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro c _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  split_ifs <;> simp_all

/--
---
conclusion: Lax342547.RecordCollision.key_record_mass_nonneg
---
-/
theorem key_record_mass_nonneg {Ω Q C : Type} [Fintype Ω]
    (ρ : Ω → ℝ) (key : Ω → Q) (record : Ω → C) (accept : Ω → Prop)
    (hρ : ∀ ω, 0 ≤ ρ ω) (q : Q) (c : C) : 0 ≤ keyRecordMass ρ key record accept q c := by
  classical
  unfold keyRecordMass recordMass cellMass
  apply Finset.sum_nonneg
  intro ω _
  split_ifs <;> first | exact hρ ω | exact le_rfl

/--
---
conclusion: Lax342547.RecordCollision.key_record_mass_subprobability
---
-/
theorem key_record_mass_subprobability {Ω Q C : Type} [Fintype Ω] [Fintype Q] [Fintype C]
    (ρ : Ω → ℝ) (key : Ω → Q) (record : Ω → C) (accept : Ω → Prop)
    (hρ : ∀ ω, 0 ≤ ρ ω) (hsum : ∑ ω, ρ ω ≤ 1) :
    (∑ q, ∑ c, keyRecordMass ρ key record accept q c) ≤ 1 := by
  simp_rw [key_record_mass_total]
  exact Lax342547Proofs.KeyMeasures.key_mass_subprobability ρ key accept hρ hsum

end Lax342547Proofs.RecordCollision
