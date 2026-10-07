import Lax342547Proofs.LabelBlocks
import Lax342547.LabelDecomposition

namespace Lax342547Proofs.LabelDecomposition

open Lax342547.MomentSpace Lax342547.FlatRank
open MomentForm FlatSelector LabelBlocks

variable {Base : Type} [Fintype Base] [DecidableEq Base] {b : ℕ}

structure FlatData (c : PointDomain Base b → Binary) (j : ℕ) where
  M : Fin b → Module.End Binary (QuotientSpace c j)
  action : ∀ a f, M a (lowClass c j f) = (form c j).ker.mkQ (shift j a f)
  adjoint : ∀ a x y, quotientPairing (form c j) (form_symm c j) (M a x) y =
    quotientPairing (form c j) (form_symm c j) x (M a y)
  P : (Fin b → Binary) → Module.End Binary (QuotientSpace c j)
  sum_eq : ∑ s, P s = 1
  idem : ∀ s, P s * P s = P s
  disjoint : ∀ s t, s ≠ t → P s * P t = 0
  eigen : ∀ a s, M a * P s = s a • P s
  dimension_sum : (∑ s, Module.finrank Binary (LinearMap.range (P s))) =
    Module.finrank Binary (QuotientSpace c j)
  active_count : Nat.card {s // P s ≠ 0} ≤ Module.finrank Binary (QuotientSpace c j)

noncomputable def flatData (c : PointDomain Base b → Binary) (j : ℕ)
    (hflat : (momentMatrix c j).rank = (momentMatrix c (j + 2)).rank) : FlatData c j := Classical.choice (by
  obtain ⟨M, hM, hadj, hid, hcomm⟩ := exists_operators c j hflat
  obtain ⟨P, hsum, hidP, horth, heigen, hdim, hcard⟩ :=
    JointProjectors.exists_joint_decomposition M hid hcomm
  exact ⟨⟨M, hM, hadj, P, hsum, hidP, horth, heigen, hdim, hcard⟩⟩)

theorem FlatData.right_eigen {c : PointDomain Base b → Binary} {j : ℕ} (D : FlatData c j)
    (a : Fin b) (s : Fin b → Binary) : D.P s * D.M a = s a • D.P s :=
  JointProjectors.right_eigen D.M D.P D.sum_eq D.idem D.disjoint D.eigen a s

theorem FlatData.orthogonal {c : PointDomain Base b → Binary} {j : ℕ} (D : FlatData c j)
    (s t : Fin b → Binary) (hst : s ≠ t) (x y : QuotientSpace c j) :
    quotientPairing (form c j) (form_symm c j) (D.P s x) (D.P t y) = 0 :=
  JointProjectors.different_labels_orthogonal _ D.M D.adjoint D.P D.eigen s t hst x y

noncomputable def extendedVector (c : PointDomain Base b → Binary) (j : ℕ) (D : FlatData c j)
    (degree : ℕ) (i : SelectorCoordinates b degree × Option Base) : QuotientSpace c j :=
  ∑ s, selectorEval s i.1 • D.P s (baseClass c j i.2)

noncomputable def extendedMatrix (c : PointDomain Base b → Binary) (j : ℕ) (D : FlatData c j)
    (degree : ℕ) : Matrix (SelectorCoordinates b degree × Option Base)
      (SelectorCoordinates b degree × Option Base) Binary :=
  GramRank.gram (quotientPairing (form c j) (form_symm c j)) (extendedVector c j D degree)

theorem extendedVector_projected (c : PointDomain Base b → Binary) (j : ℕ) (D : FlatData c j)
    (degree : ℕ) (i : SelectorCoordinates b degree × Option Base) (s : Fin b → Binary) :
    D.P s (extendedVector c j D degree i) = selectorEval s i.1 • D.P s (baseClass c j i.2) := by
  classical
  unfold extendedVector
  rw [map_sum, Finset.sum_eq_single s]
  · rw [map_smul]
    exact congrArg (selectorEval s i.1 • ·) (LinearMap.congr_fun (D.idem s) (baseClass c j i.2))
  · intro t _ hts
    rw [map_smul]
    have hz : D.P s (D.P t (baseClass c j i.2)) = 0 :=
      LinearMap.congr_fun (D.disjoint s t (Ne.symm hts)) _
    rw [hz, smul_zero]
  · simp

theorem extendedMatrix_entry (c : PointDomain Base b → Binary) (j : ℕ) (D : FlatData c j)
    (degree : ℕ) (i k : SelectorCoordinates b degree × Option Base) :
    extendedMatrix c j D degree i k =
      ∑ s, selectorEval s i.1 * selectorEval s k.1 * block c j D.P s i.2 k.2 := by
  unfold extendedMatrix GramRank.gram
  rw [JointProjectors.pairing_decomposition _ D.P D.sum_eq D.orthogonal]
  apply Finset.sum_congr rfl
  intro s _
  rw [extendedVector_projected, extendedVector_projected]
  simp [block, mul_assoc, mul_left_comm]

theorem extendedMatrix_rank_le (c : PointDomain Base b → Binary) (j : ℕ) (D : FlatData c j)
    (degree : ℕ) : (extendedMatrix c j D degree).rank ≤ (momentMatrix c (j + 2)).rank := by
  exact (GramRank.rank_gram_le _ (FlatRank.quotientPairing_symm _ _) _).trans_eq
    (FlatSelector.quotient_finrank c j)

theorem extendedMatrix_hankel (c : PointDomain Base b → Binary) (j : ℕ) (D : FlatData c j)
    (degree : ℕ) : Lax342547.MomentRecovery.IsSelectorHankel (extendedMatrix c j D degree) := by
  intro S T U V i k he
  rw [extendedMatrix_entry, extendedMatrix_entry]
  apply Finset.sum_congr rfl
  intro s _
  have hp (A B : SelectorCoordinates b degree) :
      selectorEval s A * selectorEval s B = Lax342547.SelectorInterpolation.monomial (A.val ∪ B.val) s :=
    congrFun (SelectorInterpolation.monomial_mul A.val B.val) s
  rw [hp, hp, he]

theorem extendedVector_low (c : PointDomain Base b → Binary) (j : ℕ) (D : FlatData c j)
    (degree : ℕ) (S : SelectorCoordinates b degree) (hS : S.val.card ≤ j) (i : Option Base) :
    extendedVector c j D degree (S, i) = monomialClass c j S.val hS i := by
  have hsumx := LinearMap.congr_fun D.sum_eq (monomialClass c j S.val hS i)
  have he : (∑ s, D.P s (monomialClass c j S.val hS i)) = monomialClass c j S.val hS i := by
    simpa using hsumx
  simp_rw [projected_monomial c j D.M D.action D.P D.right_eigen S.val hS i] at he
  exact he

theorem extendedMatrix_low (c : PointDomain Base b → Binary) (j : ℕ) (D : FlatData c j)
    (degree : ℕ) (S T : SelectorCoordinates b degree) (hS : S.val.card ≤ j) (hT : T.val.card ≤ j)
    (i k : Option Base) :
    extendedMatrix c j D degree (S, i) (T, k) = momentMatrix c degree (S, i) (T, k) := by
  unfold extendedMatrix GramRank.gram
  rw [extendedVector_low c j D degree S hS i, extendedVector_low c j D degree T hT k,
    momentMatrix_eq_gram]
  rfl

/--
---
conclusion: Lax342547.LabelDecomposition.low_rank_label_decomposition
---
Express the matrix by point weights, find a stabilized degree, and pass to
the radical quotient. The selector shifts induce commuting self-adjoint
idempotents. Their joint projections give the label blocks; interpolation
proves the binary diagonal identities. The dimension decomposition bounds
both the number of labels and the sum of block ranks. Finally the
minimal-degree identity-submatrix obstruction recovers all higher moments.
-/
theorem low_rank_label_decomposition {Base : Type} [Fintype Base] {b degree R : ℕ}
    (w : Matrix (SelectorCoordinates b degree × Option Base)
      (SelectorCoordinates b degree × Option Base) Binary)
    (hw : w ∈ momentSpace (selectorEval (degree := degree)) Set.univ)
    (hrank : w.rank ≤ R) (hdegree : 6 * R + 4 ≤ degree) :
    ∃ L : Finset (Fin b → Binary),
    ∃ Z : (Fin b → Binary) → Matrix (Option Base) (Option Base) Binary,
      L.card ≤ R ∧ (∀ s ∈ L, Lax342547.BaseMoments.IsBaseMoment (Z s)) ∧
      (∑ s ∈ L, (Z s).rank) ≤ R ∧
      ∀ i k, w i k = ∑ s ∈ L, selectorEval s i.1 * selectorEval s k.1 * Z s i.2 k.2 := by
  classical
  obtain ⟨c, hc⟩ := exists_weights degree w hw
  subst w
  obtain ⟨j, hj, hJ, hflat⟩ := FlatSelector.exists_flat_level c degree R hrank hdegree
  let D := flatData c j hflat
  have hrj : (momentMatrix c (j + 2)).rank ≤ R := ((moment_rank_monotone c) hJ).trans hrank
  have hdim : Module.finrank Binary (QuotientSpace c j) ≤ R :=
    (FlatSelector.quotient_finrank c j).le.trans hrj
  have hcard : Nat.card {s // D.P s ≠ 0} ≤ j + 1 := D.active_count.trans (hdim.trans (by omega))
  let L : Finset (Fin b → Binary) := Finset.univ.filter (fun s => D.P s ≠ 0)
  have heq : momentMatrix c degree = extendedMatrix c j D degree := by
    apply MomentRecovery.eq_of_agree_low _ _
      (MomentRecovery.mem_momentSpace_hankel Set.univ hw)
      (extendedMatrix_hankel c j D degree) hrank ((extendedMatrix_rank_le c j D degree).trans hrj)
    intro S T i k hST
    have hS := Finset.card_le_card (Finset.subset_union_left (s₁ := S.val) (s₂ := T.val))
    have hT := Finset.card_le_card (Finset.subset_union_right (s₁ := S.val) (s₂ := T.val))
    exact (extendedMatrix_low c j D degree S T (by omega) (by omega) i k).symm
  refine ⟨L, block c j D.P, ?_, ?_, ?_, ?_⟩
  · have h := D.active_count.trans hdim
    simpa only [L, Nat.card_eq_fintype_card, Fintype.card_subtype] using h
  · intro s _
    exact block_properties c j D.M D.action D.P D.right_eigen D.sum_eq hcard s
  · calc
      (∑ s ∈ L, (block c j D.P s).rank) ≤ ∑ s, (block c j D.P s).rank :=
        Finset.sum_le_sum_of_subset (Finset.subset_univ L)
      _ ≤ ∑ s, Module.finrank Binary (LinearMap.range (D.P s)) :=
        Finset.sum_le_sum (fun s _ => block_rank_le c j D.P s)
      _ ≤ R := D.dimension_sum.le.trans hdim
  · intro i k
    rw [heq, extendedMatrix_entry]
    symm
    apply Finset.sum_subset (Finset.subset_univ L)
    intro s _ hs
    have hz : D.P s = 0 := by simpa only [L, Finset.mem_filter, Finset.mem_univ, true_and, not_not] using hs
    simp [block, hz]

end Lax342547Proofs.LabelDecomposition
