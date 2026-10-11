import Lax342547.StarRouting
import Lax342547.RankedProjection
import Lax342547Proofs.ConcreteCut
import Lax342547Proofs.ConcreteGeometry
import Lax342547Proofs.MomentSpace

namespace Lax342547Proofs.StarRouting

open Lax342547.StarRouting

set_option backward.isDefEq.respectTransparency false

open Lax342547.MomentSpace Lax342547.ConcreteGeometry Lax342547.ConcreteCut

/--
---
conclusion: Lax342547.StarRouting.matrix_sum_rank
---
-/
theorem matrix_sum_rank {I B : Type} [Fintype I] [Fintype B]
    (M : I → Matrix B B Binary) :
    (∑ i, M i).rank ≤ ∑ i, (M i).rank := by
  classical
  change Module.finrank Binary (LinearMap.range (Matrix.toLin' (∑ i, M i))) ≤ _
  rw [map_sum]
  exact Lax342547.RankedProjection.linear_sum_rank (fun i => Matrix.toLin' (M i))

/--
---
conclusion: Lax342547.StarRouting.ordered_tester_rank
---
-/
theorem ordered_tester_rank {k n b degree r : ℕ}
    (hr : 2 * r ≤ n) (c : Fin n → Lax342547.TagGeometry.Base k n) :
    (orderedTesterMatrix (b := b) (degree := degree) hr c).rank ≤ r := by
  classical
  have h := Lax342547.StarRouting.matrix_sum_rank (fun ρ : Fin r => Matrix.vecMulVec
    (Pi.single (emptySelector b degree, some (c (pairLeft hr ρ))) (1 : Binary))
    (Pi.single (emptySelector b degree, some (c (pairRight hr ρ))) (1 : Binary)))
  have hh := h.trans (Finset.sum_le_sum (fun _ _ => Matrix.rank_vecMulVec_le _ _))
  simpa only [orderedTesterMatrix, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, mul_one] using hh

/--
---
conclusion: Lax342547.StarRouting.tester_matrix_representation
---
-/
theorem tester_matrix_representation {k n b degree r : ℕ}
    (hr : 2 * r ≤ n) (c : Fin n → Lax342547.TagGeometry.Base k n) :
    matrixPair (orderedTesterMatrix (b := b) (degree := degree) hr c) = blockTester hr c := by
  classical
  change matrixPairing (∑ ρ : Fin r, _) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro ρ _
  apply LinearMap.ext
  intro W
  simp [matrixPairing, matrixPair, Matrix.vecMulVec, Pi.single_apply, matrixEntry,
    ]


open Lax342547.TagGeometry Lax342547.CutProfiles Lax342547.Atoms

/--
---
conclusion: Lax342547.StarRouting.interval_center_excluded
---
-/
theorem interval_center_excluded {k : ℕ} (d : Tag k) : d ∉ interval k d := by
  classical
  intro hd
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hd
  have hi0 : ((i.val + 1 : ℕ) : Tag k) = 0 := by
    simpa only [add_eq_left] using hi
  have hin : i.val + 1 < 2 * k + 1 := by omega
  have : i.val + 1 = 0 := Nat.eq_zero_of_dvd_of_lt ((ZMod.natCast_eq_zero_iff (i.val + 1) (2 * k + 1)).mp hi0) hin
  omega

/--
---
conclusion: Lax342547.StarRouting.ordinary_tester_disallowed_zero
---
-/
theorem ordinary_tester_disallowed_zero {k n b degree r : ℕ} (hr : 2 * r ≤ n)
    (d t l : Tag k) (hl : l ∉ interval k d) (w : Representation k n b degree) :
    blockTester hr (ordinary d t) (w.val l) = 0 := by
  classical
  rw [Lax342547Proofs.ConcreteGeometry.blockTester_apply]
  apply Finset.sum_eq_zero
  intro ρ _
  exact Lax342547Proofs.MomentSpace.entries_zero selectorEval
    (Lax342547Proofs.ConcreteCut.representative_mem w l) _ _ (Or.inl hl)

/--
---
conclusion: Lax342547.StarRouting.star_cut_sum
---
-/
theorem star_cut_sum {k : ℕ} {X : Type} [AddCommGroup X] [Module Binary X]
    (w : Tag k → X) (l : Tag k) :
    (∑ e : {e : Component (Tag k) // l ∈ e.val}, ∑ t ∈ e.val.val, w t) =
      ∑ t : {t : Tag k // t ≠ l}, w t.val := by
  classical
  rw [← Equiv.sum_comp (incidentEquiv l)]
  change (∑ t : {t : Tag k // t ≠ l}, ∑ a ∈ ({l, t.val} : Finset (Tag k)), w a) = _
  have hp (t : {t : Tag k // t ≠ l}) :
      (∑ a ∈ ({l, t.val} : Finset (Tag k)), w a) = w l + w t.val :=
    Finset.sum_pair t.property.symm
  simp only [hp]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ]
  have hc : Fintype.card {t : Tag k // t ≠ l} = 2 * k := by
    rw [Fintype.card_subtype_compl (fun t : Tag k => t = l), Fintype.card_subtype_eq]
    simp [Tag, ZMod.card]
  have hz (x : X) : (2 : ℕ) • x = 0 := by rw [two_smul, ZModModule.add_self]
  rw [hc, mul_smul, hz, zero_add]



/--
---
conclusion: Lax342547.StarRouting.incidence_sum
---
-/
theorem incidence_sum {k : ℕ} {X : Type} [AddCommMonoid X]
    (F : Tag k → Component (Tag k) → X) :
    (∑ e, ∑ d ∈ e.val, F d e) = ∑ d, ∑ e : {e : Component (Tag k) // d ∈ e.val}, F d e.val := by
  classical
  have he (e : Component (Tag k)) : (∑ d ∈ e.val, F d e) =
      ∑ d : Tag k, if d ∈ e.val then F d e else 0 := (Fintype.sum_ite_mem e.val _).symm
  simp only [he]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp) _

/--
---
conclusion: Lax342547.StarRouting.star_matrix_representation
---
-/
theorem star_matrix_representation {k n b degree r : ℕ} (hr : 2 * r ≤ n)
    (c : Tag k → Fin n → Base k n) (coeff : Tag k → Binary)
    (w : Representation k n b degree) :
    (∑ e, matrixPair (starMatrix (b := b) (degree := degree) hr c coeff e)
      ((representationCut k n b degree w) e)) =
    ∑ d, coeff d * ∑ l : {l : Tag k // l ≠ d}, blockTester hr (c d) (w.val l.val) := by
  classical
  have hrep (d : Tag k) : matrixPairing (orderedTesterMatrix (b := b) (degree := degree) hr (c d)) = blockTester hr (c d) :=
    Lax342547.StarRouting.tester_matrix_representation hr (c d)
  simp only [starMatrix]
  have he (e : Component (Tag k)) :
      matrixPair (∑ d ∈ e.val, coeff d • orderedTesterMatrix (b := b) (degree := degree) hr (c d))
        ((representationCut k n b degree w) e) =
      ∑ d ∈ e.val, coeff d * blockTester hr (c d) ((representationCut k n b degree w) e) := by
    change matrixPairing (∑ d ∈ e.val, _) _ = _
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
      hrep, smul_eq_mul]
  simp only [he]
  rw [Lax342547.StarRouting.incidence_sum]
  apply Finset.sum_congr rfl
  intro d _
  rw [← Finset.mul_sum, ← map_sum]
  congr 1
  change blockTester hr (c d) (∑ e : {e : Component (Tag k) // d ∈ e.val},
    ∑ t ∈ e.val.val, w.val t) = _
  rw [Lax342547.StarRouting.star_cut_sum, map_sum]



/--
---
conclusion: Lax342547.StarRouting.matrix_smul_rank
---
-/
theorem matrix_smul_rank {B : Type} [Fintype B] (M : Matrix B B Binary) (a : Binary) :
    (a • M).rank ≤ M.rank := by
  fin_cases a <;> simp

/--
---
conclusion: Lax342547.StarRouting.matrix_add_rank
---
-/
theorem matrix_add_rank {B : Type} [Fintype B] (M Q : Matrix B B Binary) :
    (M + Q).rank ≤ M.rank + Q.rank := by
  have h := Lax342547.StarRouting.matrix_sum_rank (fun i : Fin 2 => if i = 0 then M else Q)
  simpa [Fin.sum_univ_two] using h

/--
---
conclusion: Lax342547.StarRouting.matrix_finset_sum_rank
---
-/
theorem matrix_finset_sum_rank {I B : Type} [Fintype B] (s : Finset I)
    (M : I → Matrix B B Binary) (R : ℕ) (hM : ∀ i ∈ s, (M i).rank ≤ R) :
    (∑ i ∈ s, M i).rank ≤ s.card * R := by
  classical
  let := Finset.Subtype.fintype s
  rw [Finset.sum_subtype (F := Finset.Subtype.fintype s) s (by intro i; rfl)]
  have h := Lax342547.StarRouting.matrix_sum_rank (fun i : {i // i ∈ s} => M i.val)
  have h' : (∑ i : {i // i ∈ s}, (M i.val).rank) ≤ ∑ _ : {i // i ∈ s}, R :=
    Finset.sum_le_sum (fun i _ => hM i.val i.property)
  simpa using h.trans h'

/--
---
conclusion: Lax342547.StarRouting.star_matrix_rank
---
-/
theorem star_matrix_rank {k n b degree r : ℕ} (hr : 2 * r ≤ n)
    (c : Tag k → Fin n → Base k n) (coeff : Tag k → Binary) (e : Component (Tag k)) :
    (starMatrix (b := b) (degree := degree) hr c coeff e).rank ≤ 2 * r := by
  classical
  have h := Lax342547.StarRouting.matrix_finset_sum_rank e.val (fun d => coeff d •
    orderedTesterMatrix (b := b) (degree := degree) hr (c d)) r
    (fun d _ => (Lax342547.StarRouting.matrix_smul_rank _ _).trans (Lax342547.StarRouting.ordered_tester_rank hr (c d)))
  simpa only [starMatrix, e.property] using h

end Lax342547Proofs.StarRouting
