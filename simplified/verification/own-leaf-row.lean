import Lax793645Proofs.Simplifications.OnePreparedLinearRank

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open LinearMap Module Function
noncomputable section
variable {p : Shape} {n N : ℕ}

/-- Fix a space of ambient frequencies of dimension greater than the free input.
Each frame can select a nonzero character from it which is one on all its
free inputs. Each frequency fixed before sampling the frame instead has
exponentially small mean. -/
theorem own_leaf_row_character (m : Mixer p n)
    (hroom : Fintype.card (Row p n) + 2*p.h + 1 ≤ N) (hN : 4 ≤ N)
    (J : Vec (Fin n) →ₗ[F] OneFull p n) (hJ : Injective J)
    (H : Space (Comp p.g → Vec (HyperbolicIdx N))) (hH : n < dim H) :
    ∃ row : OneOrient p n N → H,
      (∀ o, (row o).val ≠ 0 ∧
          avg unif (fun z => wsign (oneMixedRow J o (row o).val z)) = 1) ∧
      ∀ ξ : H, ξ.val ≠ 0 →
        avg (oneRaw m N) (fun o => avg unif (fun z => wsign (oneMixedRow J o ξ.val z)))
          ≤ 8*bp (-(n : ℝ)) := by
  classical
  have key (o : OneOrient p n N) : ∃ ξ : H, ξ.val ≠ 0 ∧ oneMixedRow J o ξ.val = 0 := by
    let pull := (oneMixedRow J o).comp H.subtype
    have hker : ker pull ≠ ⊥ := by
      intro h
      have hd := LinearMap.finrank_le_finrank_of_injective (LinearMap.ker_eq_bot.mp h)
      have hdim : dim (Module.Dual F (Vec (Fin n))) = n := by
        rw [dim, Subspace.dual_finrank_eq]
        exact (dim_vec (Fin n)).trans (Fintype.card_fin n)
      exact (not_le_of_gt hH) (hd.trans_eq hdim)
    obtain ⟨ξ,hξ,hne⟩ := (ker pull).ne_bot_iff.mp hker
    exact ⟨ξ, fun hz => hne (Subtype.ext hz), hξ⟩
  choose row hn hz using key
  refine ⟨row,fun o => ⟨hn o,?_⟩,fun ξ hξ => ?_⟩
  · rw [wsign_lin,ind_one (hz o)]
  · simp_rw [wsign_lin]
    exact one_independent_row m hroom hN J hJ ξ.val hξ 0

end
end Lax793645Proofs.Simplifications

#print axioms Lax793645Proofs.Simplifications.own_leaf_row_character
