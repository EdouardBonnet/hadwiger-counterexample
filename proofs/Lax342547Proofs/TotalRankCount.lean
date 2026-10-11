import Lax342547.TotalRankCount
import Lax342547Proofs.LowRankCounting
import Mathlib.Data.Fintype.Card

namespace Lax342547Proofs.TotalRankCount
open Lax342547.TotalRankCount

set_option backward.isDefEq.respectTransparency false
open Lax342547.MomentSpace
open scoped BigOperators

/--
---
conclusion: Lax342547.TotalRankCount.exists_rank_factors
---
-/
theorem exists_rank_factors {e I J : Type} [Fintype e] [Fintype I] [Fintype J]
    (r : ℕ) (A : e → Matrix I J Binary) (hA : ∑ i, (A i).rank ≤ r) :
    ∃ z : Σ a : RankBudgets e r, Factors I J r a, reconstruct r z = A := by
  classical
  have heach (i : e) : (A i).rank ≤ r :=
    (Finset.single_le_sum (fun j _ => Nat.zero_le (A j).rank) (Finset.mem_univ i)).trans hA
  let a : RankBudgets e r := ⟨fun i => ⟨(A i).rank,by have hh := heach i; omega⟩,hA⟩
  have hex (i : e) : ∃ X : Matrix I (Fin (a.val i).val) Binary,
      ∃ Y : Matrix (Fin (a.val i).val) J Binary, X*Y = A i :=
    Lax342547Proofs.LowRankCounting.factorization (A i) (A i).rank le_rfl
  choose X Y hXY using hex
  exact ⟨⟨a,X,Y⟩,funext hXY⟩

/--
---
conclusion: Lax342547.TotalRankCount.factor_card_bound
---
-/
theorem factor_card_bound {e I J : Type} [Fintype e] [Fintype I] [Fintype J]
    [DecidableEq e] [DecidableEq I] [DecidableEq J] (r : ℕ) (a : RankBudgets e r) :
    Fintype.card (Factors I J r a) ≤ 2^((Fintype.card I+Fintype.card J)*r) := by
  classical
  simp only [Factors,Fintype.card_prod,Fintype.card_pi,Matrix,Fintype.card_fun,Fintype.card_fin,ZMod.card,Finset.prod_const,Finset.card_univ,← pow_mul]
  rw [← Finset.prod_mul_distrib]
  have he : (∏ i, (2^((a.val i).val*Fintype.card I)*2^(Fintype.card J*(a.val i).val))) =
      2^((Fintype.card I+Fintype.card J)*∑ i, (a.val i).val) := by
    simp_rw [← pow_add]
    rw [Finset.prod_pow_eq_pow_sum]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he]
  exact Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left _ a.property)

/--
---
conclusion: Lax342547.TotalRankCount.total_rank_card
---
-/
theorem total_rank_card {e I J : Type} [Fintype e] [Fintype I] [Fintype J]
    [DecidableEq e] [DecidableEq I] [DecidableEq J] (r : ℕ) :
    Fintype.card {A : e → Matrix I J Binary // ∑ i, (A i).rank ≤ r} ≤
      (r+1)^Fintype.card e*2^((Fintype.card I+Fintype.card J)*r) := by
  classical
  let C := {A : e → Matrix I J Binary // ∑ i, (A i).rank ≤ r}
  have hex (A : C) := exists_rank_factors r A.val A.property
  choose f hf using hex
  have hinj : Function.Injective f := by
    intro A B he
    apply Subtype.ext
    exact (hf A).symm.trans ((congrArg (reconstruct r) he).trans (hf B))
  have hh := Fintype.card_le_of_injective f hinj
  have ha : Fintype.card (RankBudgets e r) ≤ (r+1)^Fintype.card e := by
    simpa only [Fintype.card_fun,Fintype.card_fin] using
      Fintype.card_le_of_injective (fun a : RankBudgets e r => a.val) Subtype.val_injective
  calc
    _ ≤ Fintype.card (Σ a : RankBudgets e r, Factors I J r a) := hh
    _ = ∑ a : RankBudgets e r, Fintype.card (Factors I J r a) := Fintype.card_sigma
    _ ≤ ∑ _ : RankBudgets e r, 2^((Fintype.card I+Fintype.card J)*r) :=
      Finset.sum_le_sum (fun a _ => factor_card_bound r a)
    _ = Fintype.card (RankBudgets e r)*2^((Fintype.card I+Fintype.card J)*r) := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ ha

end Lax342547Proofs.TotalRankCount
