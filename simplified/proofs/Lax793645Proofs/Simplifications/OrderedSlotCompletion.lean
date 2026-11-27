import Lax793645Proofs.Simplifications.BlockRankCompletion

/-! A symmetric Gram pattern can be completed by ordering the slots inside
each batch. For a pair of distinct slots, copy one orientation and transpose
it into the other. For equal slots the scalar diagonal already has symmetry. -/

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix Function
noncomputable section
variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

theorem ordered_slot_completion (P : J → J → Prop) [DecidableRel P]
    (hP : ∀ u v, P u v → P v u) (M : Avenue I J)
    (hM : ∀ x y, ¬P x.2 y.2 → M x y = 0) (hs : Mᵀ = M) :
    ∃ D R : Avenue I J, M = D+R ∧ Dᵀ = D ∧ Rᵀ = R ∧
      (∀ x y, x.1 ≠ y.1 → D x y = 0) ∧
      (∀ x y, ¬P x.2 y.2 → D x y = 0 ∧ R x y = 0) ∧
      R.rank ≤ 2*Fintype.card J*(1+4*Fintype.card J)*peak M := by
  classical
  obtain ⟨B,U,hMU,hB,hr⟩ := block_rank_completion M
  have off (x y : I × J) (h : x.1 ≠ y.1) : U x y = M x y := by
    simp only [hMU, Matrix.add_apply, hB x y h, zero_add]
  have sym (x y : I × J) : M y x = M x y := congrFun (congrFun hs x) y
  let e := Fintype.equivFin J
  let V := maskBlockPattern (fun a b => P a b ∧ e a ≤ e b) U
  let W := maskBlockPattern (fun a b => P a b ∧ e a < e b) U
  let R := V + Wᵀ
  have entry (x y : I × J) :
      R x y = if P x.2 y.2 then (if e x.2 ≤ e y.2 then U x y else U y x) else 0 := by
    change (if P x.2 y.2 ∧ e x.2 ≤ e y.2 then U x y else 0) +
      (if P y.2 x.2 ∧ e y.2 < e x.2 then U y x else 0) = _
    have eqP : P y.2 x.2 ↔ P x.2 y.2 := ⟨hP _ _,hP _ _⟩
    by_cases hp : P x.2 y.2 <;> by_cases he : e x.2 ≤ e y.2 <;> simp [eqP,hp,he,lt_iff_not_ge]
  have same (x y : I × J) (hh : x.1 ≠ y.1) : R x y = M x y := by
    rw [entry,off x y hh,off y x (Ne.symm hh),sym x y,ite_self]
    by_cases hp : P x.2 y.2
    · simp [hp]
    · simp [hp,hM x y hp]
  have hR : Rᵀ = R := by
    ext x y
    change R y x = R x y
    by_cases hh : x.1 = y.1
    · have eqP : P y.2 x.2 ↔ P x.2 y.2 := ⟨hP _ _,hP _ _⟩
      rcases lt_trichotomy (e x.2) (e y.2) with ht|he|ht
      · simp [entry,eqP,ht.le,not_le.mpr ht]
      · have hxy : x = y := Prod.ext hh (e.injective he)
        rw [hxy]
      · simp [entry,eqP,ht.le,not_le.mpr ht]
    · rw [same _ _ (Ne.symm hh),same _ _ hh,sym x y]
  refine ⟨M+R,R,?_,?_,hR,?_,?_,?_⟩
  · rw [add_assoc,char_two,add_zero]
  · rw [transpose_add,hs,hR]
  · intro x y hh
    rw [Matrix.add_apply,same _ _ hh,char_two]
  · intro x y hp
    have hz : R x y = 0 := by simp [entry,hp]
    exact ⟨by rw [Matrix.add_apply,hM x y hp,hz,zero_add],hz⟩
  · have hV : V.rank ≤ Fintype.card J * U.rank := mask_block_rank _ U
    have hW : W.rank ≤ Fintype.card J * U.rank := mask_block_rank _ U
    have hsum := mrk_add_le V Wᵀ
    rw [rank_transpose] at hsum
    calc
      R.rank ≤ 2*Fintype.card J*U.rank := by dsimp only [R]; nlinarith only [hsum,hV,hW]
      _ ≤ _ := by simpa only [mul_assoc] using Nat.mul_le_mul_left (2*Fintype.card J) hr

end
end Lax793645Proofs.Simplifications
