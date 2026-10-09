import Lax342547.LowRankCounting
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Tactic.Ring

namespace Lax342547Proofs.LowRankCounting

set_option backward.isDefEq.respectTransparency false

/--
---
conclusion: Lax342547.LowRankCounting.factorization
---
Choose coordinates on the image of M. Restriction from r coordinates
onto those image coordinates is onto; split that surjection and express
the two resulting linear maps as matrices.
-/
theorem factorization {K I J : Type} [Field K] [Fintype I] [Fintype J]
    (M : Matrix I J K) (r : ℕ) (hr : M.rank ≤ r) :
    ∃ X : Matrix I (Fin r) K, ∃ Y : Matrix (Fin r) J K, X * Y = M := by
  classical
  let S := LinearMap.range M.mulVecLin
  let e := (Module.finBasis K S).equivFun
  have hd : Module.finrank K S ≤ r := hr
  let π : (Fin r → K) →ₗ[K] (Fin (Module.finrank K S) → K) := LinearMap.funLeft K K (Fin.castLE hd)
  have hπ : Function.Surjective π := by
    intro v
    refine ⟨fun j => if hj : j.val < Module.finrank K S then v ⟨j.val, hj⟩ else 0, ?_⟩
    ext i
    simp [π, LinearMap.funLeft_apply, i.isLt]
  let p : (Fin r → K) →ₗ[K] S := e.symm.toLinearMap.comp π
  have hp : Function.Surjective p := e.symm.surjective.comp hπ
  obtain ⟨q, hq⟩ := p.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hp)
  have he : (S.subtype.comp p).comp (q.comp M.mulVecLin.rangeRestrict) = M.mulVecLin := calc
    _ = S.subtype.comp ((p.comp q).comp M.mulVecLin.rangeRestrict) := by ext; rfl
    _ = S.subtype.comp M.mulVecLin.rangeRestrict := by rw [hq, LinearMap.id_comp]
    _ = _ := rfl
  refine ⟨(S.subtype.comp p).toMatrix', (q.comp M.mulVecLin.rangeRestrict).toMatrix', ?_⟩
  rw [← LinearMap.toMatrix'_comp, he]
  exact LinearMap.toMatrix'_toLin' M

open Lax342547.MomentSpace
open scoped ENNReal

/--
---
conclusion: Lax342547.LowRankCounting.card_low_rank
---
Choose one factorization for each low-rank matrix. Its two factors encode
it injectively and use (|I|+|J|)r binary entries.
-/
theorem card_low_rank {I J : Type} [Fintype I] [Fintype J] (r : ℕ) :
    Nat.card {M : Matrix I J Binary // M.rank ≤ r} ≤ 2 ^ ((Fintype.card I + Fintype.card J) * r) := by
  classical
  let T := {M : Matrix I J Binary // M.rank ≤ r}
  have hf (M : T) := factorization M.val r M.property
  choose X Y hXY using hf
  have hi : Function.Injective (fun M : T => (X M, Y M)) := by
    intro M N he
    apply Subtype.ext
    rw [← hXY M, ← hXY N, (Prod.mk.inj he).1, (Prod.mk.inj he).2]
  calc
    Nat.card T = Fintype.card T := Nat.card_eq_fintype_card
    _ ≤ Fintype.card (Matrix I (Fin r) Binary × Matrix (Fin r) J Binary) :=
      Fintype.card_le_of_injective _ hi
    _ = _ := by
      change Fintype.card ((I → Fin r → Binary) × (Fin r → J → Binary)) = _
      simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Binary, ZMod.card,
        ← pow_mul, ← pow_add]
      congr 1
      ring

/--
---
conclusion: Lax342547.LowRankCounting.uniform_low_rank_bound
---
Divide the checked low-rank matrix count by the size of the full binary
matrix space to obtain the exact finite uniform probability bound.
-/
theorem uniform_low_rank_bound {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (r : ℕ) : (PMF.uniformOfFintype (Matrix I J Binary)).toOuterMeasure {M | M.rank ≤ r} ≤
      (2 : ℝ≥0∞) ^ ((Fintype.card I + Fintype.card J) * r) / 2 ^ (Fintype.card I * Fintype.card J) := by
  classical
  rw [PMF.toOuterMeasure_uniformOfFintype_apply]
  have h : (Fintype.card {M : Matrix I J Binary // M.rank ≤ r} : ℝ≥0∞) ≤
      2 ^ ((Fintype.card I + Fintype.card J) * r) := by
    exact_mod_cast (show Fintype.card {M : Matrix I J Binary // M.rank ≤ r} ≤ _ from
      by simpa only [Nat.card_eq_fintype_card] using card_low_rank (I := I) (J := J) r)
  have hcard : (Fintype.card (Matrix I J Binary) : ℝ≥0∞) = 2 ^ (Fintype.card I * Fintype.card J) := by
    change (Fintype.card (I → J → Binary) : ℝ≥0∞) = _
    simp [Binary, ZMod.card, ← pow_mul, Nat.mul_comm]
  rw [hcard]
  exact ENNReal.div_le_div_right h _

end Lax342547Proofs.LowRankCounting
