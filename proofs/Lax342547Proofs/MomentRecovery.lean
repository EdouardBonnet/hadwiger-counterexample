import Lax342547.MomentRecovery
import Lax342547Proofs.SelectorInterpolation

namespace Lax342547Proofs.MomentRecovery

open Lax342547.MomentSpace Lax342547.MomentRecovery
open Lax342547.SelectorInterpolation

variable {Base : Type} {b degree : ℕ}

theorem pointMoment_hankel (s : Fin b → Binary) (z : Base → Binary) :
    IsSelectorHankel (pointMoment (selectorEval (degree := degree)) s z) := by
  intro S T U V i j he
  have hp (A B : SelectorCoordinates b degree) :
      selectorEval s A * selectorEval s B = monomial (A.val ∪ B.val) s :=
    congrFun (SelectorInterpolation.monomial_mul A.val B.val) s
  change (selectorEval s S * baseEval z i) * (selectorEval s T * baseEval z j) =
    (selectorEval s U * baseEval z i) * (selectorEval s V * baseEval z j)
  rw [mul_mul_mul_comm, hp, mul_mul_mul_comm, hp, he]

theorem mem_momentSpace_hankel (A : Set Base)
    {w : Matrix (SelectorCoordinates b degree × Option Base)
      (SelectorCoordinates b degree × Option Base) Binary}
    (hw : w ∈ momentSpace (selectorEval (degree := degree)) A) : IsSelectorHankel w := by
  induction hw using Submodule.span_induction with
  | mem w hw => obtain ⟨s, z, _, rfl⟩ := hw; exact pointMoment_hankel s z
  | zero => exact fun _ _ _ _ _ _ _ => rfl
  | add w v _ _ hw hv =>
    exact fun S T U V i j he => congrArg₂ (· + ·) (hw S T U V i j he) (hv S T U V i j he)
  | smul c w _ hw =>
    exact fun S T U V i j he => congrArg (c * ·) (hw S T U V i j he)

theorem off_diagonal_union_card_lt {U A B : Finset (Fin b)}
    (hA : A ⊆ U) (hB : B ⊆ U) (hcard : A.card = B.card) (hne : A ≠ B) :
    (A ∪ (U \ B)).card < U.card := by
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.union_subset hA Finset.sdiff_subset, ?_⟩
  intro he
  have hBA : B ⊆ A := by
    intro x hx
    have hxu : x ∈ A ∪ (U \ B) := he.symm ▸ hB hx
    rcases Finset.mem_union.mp hxu with hxA | hxB
    · exact hxA
    · exact False.elim ((Finset.mem_sdiff.mp hxB).2 hx)
  exact hne (Finset.eq_of_subset_of_card_le hBA hcard.le).symm

theorem binary_eq_one_of_ne_zero (x : Binary) (hx : x ≠ 0) : x = 1 := by
  fin_cases x
  · exact False.elim (hx rfl)
  · rfl

theorem choose_le_rank_of_minimal [Fintype Base]
    (w : Matrix (SelectorCoordinates b degree × Base)
      (SelectorCoordinates b degree × Base) Binary)
    (hH : IsSelectorHankel w) (S T : SelectorCoordinates b degree) (i j : Base)
    (hne : w (S, i) (T, j) ≠ 0)
    (hmin : ∀ (A B : SelectorCoordinates b degree) (k l : Base),
      (A.val ∪ B.val).card < (S.val ∪ T.val).card → w (A, k) (B, l) = 0) :
    (S.val ∪ T.val).card.choose ((S.val ∪ T.val).card / 2) ≤ w.rank := by
  classical
  let U := S.val ∪ T.val
  let d := U.card
  let Half := {A : Finset (Fin b) // A ∈ U.powersetCard (d / 2)}
  have hhalf (A : Half) : A.val ⊆ U ∧ A.val.card = d / 2 :=
    Finset.mem_powersetCard.mp A.property
  have hd : d ≤ 2 * degree := by
    have hc := Finset.card_union_le S.val T.val
    have hS := S.property
    have hT := T.property
    dsimp [d, U]
    omega
  let row : Half → SelectorCoordinates b degree × Base :=
    fun A => (⟨A.val, by have := (hhalf A).2; omega⟩, i)
  let col : Half → SelectorCoordinates b degree × Base :=
    fun A => (⟨U \ A.val, by
      rw [Finset.card_sdiff_of_subset (hhalf A).1, (hhalf A).2]
      change d - d / 2 ≤ degree
      omega⟩, j)
  have hsub : w.submatrix row col = (1 : Matrix Half Half Binary) := by
    ext A B
    change w (row A) (col B) = _
    by_cases he : A = B
    · subst B
      rw [Matrix.one_apply_eq]
      have hu : A.val ∪ (U \ A.val) = S.val ∪ T.val :=
        Finset.union_sdiff_of_subset (hhalf A).1
      exact (hH _ _ S T i j hu).trans (binary_eq_one_of_ne_zero _ hne)
    · rw [Matrix.one_apply_ne he]
      exact hmin _ _ i j (off_diagonal_union_card_lt (hhalf A).1 (hhalf B).1
        ((hhalf A).2.trans (hhalf B).2.symm) (fun h => he (Subtype.ext h)))
  have hr := Matrix.rank_submatrix_le w row col
  rw [hsub, Matrix.rank_one] at hr
  simpa only [Half, Fintype.card_coe, Finset.card_powersetCard] using hr

/--
---
conclusion: Lax342547.MomentRecovery.eq_zero_of_rank_le
---
Choose a nonzero moment of least selector degree d. Complementary subsets
of its support give an identity submatrix of size binomial(d, floor(d/2)),
which is at least d. The rank bound forces d into the vanishing degrees.
-/
theorem eq_zero_of_rank_le {Base : Type} [Fintype Base] {b degree r : ℕ}
    (w : Matrix (SelectorCoordinates b degree × Base)
      (SelectorCoordinates b degree × Base) Binary)
    (hH : IsSelectorHankel w) (hrank : w.rank ≤ r)
    (hlow : ∀ (S T : SelectorCoordinates b degree) (i j : Base),
      (S.val ∪ T.val).card ≤ r → w (S, i) (T, j) = 0) : w = 0 := by
  classical
  by_contra hw
  have hex : ∃ d : ℕ, ∃ (S T : SelectorCoordinates b degree) (i j : Base),
      (S.val ∪ T.val).card = d ∧ w (S, i) (T, j) ≠ 0 := by
    by_contra h
    apply hw
    ext ⟨S, i⟩ ⟨T, j⟩
    by_contra hentry
    exact h ⟨_, S, T, i, j, rfl, hentry⟩
  obtain ⟨S, T, i, j, hdegree, hne⟩ := Nat.find_spec hex
  have hmin (A B : SelectorCoordinates b degree) (k l : Base)
      (hsmall : (A.val ∪ B.val).card < (S.val ∪ T.val).card) : w (A, k) (B, l) = 0 := by
    by_contra hentry
    have := Nat.find_min' hex ⟨A, B, k, l, rfl, hentry⟩
    omega
  have hchoose := choose_le_rank_of_minimal w hH S T i j hne hmin
  have hmiddle : (S.val ∪ T.val).card ≤
      (S.val ∪ T.val).card.choose ((S.val ∪ T.val).card / 2) := by
    simpa using Nat.choose_le_middle 1 (S.val ∪ T.val).card
  exact hne (hlow S T i j (hmiddle.trans (hchoose.trans hrank)))

theorem rank_add_le {K I J : Type} [Field K] [Fintype I] [Fintype J] (w v : Matrix I J K) :
    (w + v).rank ≤ w.rank + v.rank := by
  rw [Matrix.rank, Matrix.mulVecLin_add, Matrix.rank, Matrix.rank]
  calc
    Module.finrank K (LinearMap.range (w.mulVecLin + v.mulVecLin)) ≤
        Module.finrank K (LinearMap.range w.mulVecLin ⊔ LinearMap.range v.mulVecLin :
          Submodule K (I → K)) :=
      Submodule.finrank_mono (LinearMap.range_add_le w.mulVecLin v.mulVecLin)
    _ ≤ _ := Submodule.finrank_add_le_finrank_add_finrank
      (LinearMap.range w.mulVecLin) (LinearMap.range v.mulVecLin)

/--
---
conclusion: Lax342547.MomentRecovery.eq_of_agree_low
---
The sum of the two matrices is Hankel, has rank at most the sum of their
ranks, and vanishes in all degrees up to that bound. Apply the minimal-degree
rank obstruction. Over the binary field its vanishing is equality.
-/
theorem eq_of_agree_low {Base : Type} [Fintype Base] {b degree r₁ r₂ : ℕ}
    (w v : Matrix (SelectorCoordinates b degree × Base)
      (SelectorCoordinates b degree × Base) Binary)
    (hw : IsSelectorHankel w) (hv : IsSelectorHankel v)
    (hrw : w.rank ≤ r₁) (hrv : v.rank ≤ r₂)
    (hlow : ∀ (S T : SelectorCoordinates b degree) (i j : Base),
      (S.val ∪ T.val).card ≤ r₁ + r₂ → w (S, i) (T, j) = v (S, i) (T, j)) : w = v := by
  have hH : IsSelectorHankel (w + v) := fun S T U V i j he =>
    congrArg₂ (· + ·) (hw S T U V i j he) (hv S T U V i j he)
  have hr : (w + v).rank ≤ r₁ + r₂ :=
    (rank_add_le w v).trans (Nat.add_le_add hrw hrv)
  have hz := Lax342547.MomentRecovery.eq_zero_of_rank_le (w + v) hH hr (fun S T i j hc => by
    change w (S, i) (T, j) + v (S, i) (T, j) = 0
    rw [hlow S T i j hc, ZModModule.add_self])
  have he : w + v = v + v := hz.trans (ZModModule.add_self v).symm
  exact add_right_cancel he

end Lax342547Proofs.MomentRecovery
