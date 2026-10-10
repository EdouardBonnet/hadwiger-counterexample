import Lax342547.FiniteCollision
import Lax342547Proofs.RecordCollision
import Lax342547Proofs.ParameterCellAveraging
import Lax342547Proofs.CollisionExponents

namespace Lax342547Proofs.FiniteCollision
open Lax342547.FiniteCollision

set_option backward.isDefEq.respectTransparency false
open Lax342547.RecordCollision Lax342547.KeyMeasures Lax342547.CellAveraging
open Lax342547.RetainedImages Lax342547.ParameterCellAveraging Lax342547.CollisionPruning

/--
---
conclusion: Lax342547.FiniteCollision.average_sub
---
-/
theorem average_sub {A B : Type} [Fintype A] [Fintype B]
    (p : A → ℝ) (q : B → ℝ) (f g : A → B → ℝ) :
    average p q (fun x y => f x y - g x y) = average p q f - average p q g := by
  unfold average
  simp_rw [mul_sub, Finset.sum_sub_distrib]

/--
---
conclusion: Lax342547.FiniteCollision.independent_key_overlap
---
-/
theorem independent_key_overlap {A B ΩA ΩB Q : Type} [Fintype A] [Fintype B]
    [Fintype ΩA] [Fintype ΩB] [Fintype Q] [Nonempty Q]
    (p : A → ℝ) (q : B → ℝ) (α : ΩA → ℝ) (β : ΩB → ℝ)
    (keyA : A → ΩA → Q) (keyB : B → ΩB → Q)
    (acceptA : A → ΩA → Prop) (acceptB : B → ΩB → Prop) :
    uniformOverlap (acceptedDensity p α keyA acceptA) (acceptedDensity q β keyB acceptB) =
    Fintype.card Q * average p q (fun x y => ∑ z,
      keyMass α (keyA x) (acceptA x) z * keyMass β (keyB y) (acceptB y) z) := by
  rw [Lax342547Proofs.KeyMeasures.uniform_overlap_collision]
  congr 1
  unfold acceptedDensity average
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro z _
  ring

/--
---
conclusion: Lax342547.FiniteCollision.averaged_record_pruning
---
-/
theorem averaged_record_pruning {A B ΩA ΩB Q C D : Type}
    [Fintype A] [Fintype B] [Fintype ΩA] [Fintype ΩB]
    [Fintype Q] [Nonempty Q] [Fintype C] [Fintype D]
    (p : A → ℝ) (q : B → ℝ) (α : ΩA → ℝ) (β : ΩB → ℝ)
    (keyA : A → ΩA → Q) (keyB : B → ΩB → Q)
    (recordA : A → B → ΩA → C) (recordB : B → A → ΩB → D)
    (acceptA : A → ΩA → Prop) (acceptB : B → ΩB → Prop) (τ : ℝ)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ y, 0 ≤ q y)
    (hpsum : ∑ x, p x = 1) (hqsum : ∑ y, q y = 1)
    (hα : ∀ a, 0 ≤ α a) (hβ : ∀ b, 0 ≤ β b)
    (hαsum : ∑ a, α a ≤ 1) (hβsum : ∑ b, β b ≤ 1) (hτ : 0 ≤ τ) :
    uniformOverlap (acceptedDensity p α keyA acceptA) (acceptedDensity q β keyB acceptB) -
      Fintype.card Q * average p q (fun x y => retainedPairs
        (fun zc : Q × C => keyRecordMass α (keyA x) (recordA x y) (acceptA x) zc.1 zc.2)
        (fun zd : Q × D => keyRecordMass β (keyB y) (recordB y x) (acceptB y) zd.1 zd.2)
        (fun zc zd => zc.1 = zd.1) τ) ≤
      Fintype.card Q * (Fintype.card C + Fintype.card D : ℝ) * τ := by
  have h := Lax342547Proofs.CollisionPruning.averaged_pruning p q
    (fun x y z c => keyRecordMass α (keyA x) (recordA x y) (acceptA x) z c)
    (fun y x z d => keyRecordMass β (keyB y) (recordB y x) (acceptB y) z d)
    τ hτ hp hq hpsum hqsum
    (fun x y z c => Lax342547Proofs.RecordCollision.key_record_mass_nonneg α (keyA x) (recordA x y) (acceptA x) hα z c)
    (fun y x z d => Lax342547Proofs.RecordCollision.key_record_mass_nonneg β (keyB y) (recordB y x) (acceptB y) hβ z d)
    (fun x y => Lax342547Proofs.RecordCollision.key_record_mass_subprobability α (keyA x) (recordA x y) (acceptA x) hα hαsum)
    (fun y x => Lax342547Proofs.RecordCollision.key_record_mass_subprobability β (keyB y) (recordB y x) (acceptB y) hβ hβsum)
  simp_rw [Lax342547Proofs.RecordCollision.key_record_mass_total] at h
  change average p q (fun x y => _ - _) ≤ _ at h
  rw [average_sub] at h
  rw [independent_key_overlap]
  simp_rw [Lax342547Proofs.RecordCollision.retained_key_record_identity]
  have hm := mul_le_mul_of_nonneg_left h (Nat.cast_nonneg (Fintype.card Q) : (0:ℝ) ≤ _)
  nlinarith

/--
---
conclusion: Lax342547.FiniteCollision.finite_collision_lower
---
-/
theorem finite_collision_lower {A B ΩA ΩB Q C D : Type}
    [Fintype A] [Fintype B] [Fintype ΩA] [Fintype ΩB]
    [Fintype Q] [Nonempty Q] [Fintype C] [Fintype D]
    (p : A → ℝ) (q : B → ℝ) (α : ΩA → ℝ) (β : ΩB → ℝ)
    (keyA : A → ΩA → Q) (keyB : B → ΩB → Q)
    (recordA : A → B → ΩA → C) (recordB : B → A → ΩB → D)
    (acceptA : A → ΩA → Prop) (acceptB : B → ΩB → Prop)
    (H : ΩA → ΩB → Prop) (τ ε : ℝ)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ y, 0 ≤ q y)
    (hpsum : ∑ x, p x = 1) (hqsum : ∑ y, q y = 1)
    (hα : ∀ a, 0 ≤ α a) (hβ : ∀ b, 0 ≤ β b)
    (hαsum : ∑ a, α a ≤ 1) (hβsum : ∑ b, β b ≤ 1) (hτ : 0 < τ) (hε : 0 ≤ ε)
    (hloc : ∀ x y zc zd, zc.1 = zd.1 →
      τ ≤ keyRecordMass α (keyA x) (recordA x y) (acceptA x) zc.1 zc.2 →
      τ ≤ keyRecordMass β (keyB y) (recordB y x) (acceptB y) zd.1 zd.2 → ε ≤
        pairEventMass (conditionalLaw α (fun a => acceptA x a ∧ (keyA x a, recordA x y a) = zc))
          (conditionalLaw β (fun b => acceptB y b ∧ (keyB y b, recordB y x b) = zd)) H) :
    ε * (uniformOverlap (acceptedDensity p α keyA acceptA) (acceptedDensity q β keyB acceptB) -
      Fintype.card Q * (Fintype.card C + Fintype.card D : ℝ) * τ) / Fintype.card Q ≤
        pairEventMass α β H := by
  have hprune := averaged_record_pruning p q α β keyA keyB recordA recordB acceptA acceptB τ
    hp hq hpsum hqsum hα hβ hαsum hβsum hτ.le
  have hholes := Lax342547Proofs.ParameterCellAveraging.average_cell_pair_lower p q α β
    (fun x y a => (keyA x a, recordA x y a)) (fun y x b => (keyB y b, recordB y x b))
    acceptA acceptB (fun _ _ zc zd => zc.1 = zd.1) H τ ε
    hp hq hpsum hqsum hα hβ hτ hloc
  have hkeys : (0 : ℝ) < Fintype.card Q := by exact_mod_cast Fintype.card_pos
  exact Lax342547Proofs.CollisionExponents.collision_lower_from_overlap _ _ _ _ _ _
    hkeys hε hprune hholes

end Lax342547Proofs.FiniteCollision
