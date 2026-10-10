import Lax342547.BinaryPrescriptions

namespace Lax342547Proofs.BinaryPrescriptions

open Lax342547.MomentSpace Lax342547.BinaryPrescriptions

/--
---
conclusion: Lax342547.BinaryPrescriptions.realize
---
Order the finite atom indices. For the increasing order of each distinct
pair choose one allowed term, with factors one and the desired correction.
All other factors are zero. Exactly one ordered sum contributes; binary
addition cancels the old entry. Diagonal entries are unchanged.
-/
theorem realize {I Term : Type} [Fintype I] [Fintype Term]
    (allowed : I → I → Term → Prop) (hallowed : ∀ x y, ∃ t, allowed x y t)
    (T₀ M : Matrix I I Binary) (hT : ∀ x y, T₀ x y = T₀ y x)
    (hM : ∀ x y, M x y = M y x) (hdiag : ∀ x, M x x = T₀ x x) :
    ∃ L R : I → I → Term → Binary,
      (∀ x y t, ¬ allowed x y t → L x y t = 0 ∧ R x y t = 0) ∧
      ∀ x y, T₀ x y + productSum L R x y + productSum L R y x = M x y := by
  classical
  choose term hterm using hallowed
  let rank := Fintype.equivFin I
  let L : I → I → Term → Binary := fun x y t =>
    if rank x < rank y ∧ t = term x y then 1 else 0
  let R : I → I → Term → Binary := fun x y t =>
    if rank x < rank y ∧ t = term x y then M x y + T₀ x y else 0
  have hsum (x y : I) : productSum L R x y = if rank x < rank y then M x y + T₀ x y else 0 := by
    by_cases hxy : rank x < rank y <;> simp [productSum, L, R, hxy]
  refine ⟨L, R, ?_, ?_⟩
  · intro x y t ht
    have hn : t ≠ term x y := fun he => ht (he.symm ▸ hterm x y)
    simp [L, R, hn]
  · intro x y
    rw [hsum, hsum]
    rcases lt_trichotomy (rank x) (rank y) with hxy | hxy | hxy
    · simp only [hxy, if_pos, if_neg (not_lt_of_ge hxy.le), add_zero]
      rw [add_left_comm, ZModModule.add_self, add_zero]
    · have he : x = y := rank.injective hxy
      subst y
      simp [hdiag]
    · simp only [hxy, if_pos, if_neg (not_lt_of_ge hxy.le), add_zero]
      rw [hT x y, hM y x, add_left_comm, ZModModule.add_self, add_zero]

end Lax342547Proofs.BinaryPrescriptions
