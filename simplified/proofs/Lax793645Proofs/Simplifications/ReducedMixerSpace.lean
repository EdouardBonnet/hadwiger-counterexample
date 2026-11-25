import Lax793645Proofs.Simplifications.ReducedMixerVariables

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n : ℕ}

theorem reduced_factors_space {r : Comp p.g×Bool→ℕ} (P Q : ReducedParts p n r) :
    ∃ S : Space (Ray p n), (∀ i,colSp (P i) ≤ S ∧ colSp (Q i) ≤ S) ∧
      dim S ≤ 2*(∑ i, r i) := by
  classical
  have he (J : Finset (Comp p.g×Bool)) :
      ∃ S : Space (Ray p n), (∀ i∈J,colSp (P i) ≤ S ∧ colSp (Q i) ≤ S) ∧
        dim S ≤ 2*∑ i∈J,r i := by
    induction J using Finset.induction with
    | empty => exact ⟨⊥,fun _ h => (Finset.notMem_empty _ h).elim,
        (finrank_bot _ _).le.trans (Nat.zero_le _)⟩
    | insert i J hi ih =>
      obtain ⟨S,hS,h⟩ := ih
      let T := colSp (P i) ⊔ colSp (Q i)
      refine ⟨S⊔T,fun j hj => ?_, ?_⟩
      · rcases Finset.mem_insert.mp hj with rfl|hj
        · exact ⟨le_trans (show colSp _ ≤ T from le_sup_left) le_sup_right,
            le_trans (show colSp _ ≤ T from le_sup_right) le_sup_right⟩
        · exact ⟨(hS j hj).1.trans le_sup_left,(hS j hj).2.trans le_sup_left⟩
      have hh : dim T ≤ 2*r i := by
        have hp (P : ReducedParts p n r) : dim (colSp (P i)) ≤ r i := by
          rw [colSp_dim]
          exact (Matrix.rank_le_card_width (P i)).trans_eq (Fintype.card_fin _)
        rw [two_mul]
        exact (Submodule.finrank_add_le_finrank_add_finrank ..).trans (Nat.add_le_add (hp _) (hp _))
      rw [Finset.sum_insert hi]
      apply le_trans (Submodule.finrank_add_le_finrank_add_finrank ..)
      exact (Nat.add_le_add h hh).trans (by omega)
  obtain ⟨S,h,g⟩ := he Finset.univ
  exact ⟨S,fun i => h _ (Finset.mem_univ i),g⟩

end
end Lax793645Proofs.Simplifications
