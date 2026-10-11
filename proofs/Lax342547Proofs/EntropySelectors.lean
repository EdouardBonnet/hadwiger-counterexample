import Lax342547.EntropySelectors
import Lax342547.ContainerLaws
import Lax342547.RelativeEntropy

namespace Lax342547Proofs.EntropySelectors
open Lax342547.EntropySelectors

set_option backward.isDefEq.respectTransparency false
open Lax342547.RelativeEntropy Lax342547.ContainerLaws Lax342547.RetainedImages
open scoped BigOperators

/--
---
conclusion: Lax342547.EntropySelectors.heavy_neighbor_nonempty
---
-/
theorem heavy_neighbor_nonempty {U : Type} [Fintype U]
    (ρ : U → ℝ) (R : Finset U) (H : U → U → Prop) (v : U)
    (hs : ∀ x, x ∉ R → ρ x = 0) (hm : 0 < neighborMass ρ H v) : ∃ w ∈ R, H v w := by
  classical
  by_contra hn
  push Not at hn
  have hh : neighborMass ρ H v = 0 := by
    unfold neighborMass cellMass
    apply Finset.sum_eq_zero
    intro w _
    by_cases hw : w ∈ R
    · simp [hn w hw]
    · simp [hs w hw]
  rw [hh] at hm
  exact lt_irrefl 0 hm

/--
---
conclusion: Lax342547.EntropySelectors.entropy_selectors
---
-/
theorem entropy_selectors {U : Type} [Fintype U] [Nonempty U]
    (P : Set (U → ℝ)) (q : U → ℝ) (H : U → U → Prop) (ε : ℝ)
    (hc : IsCompact P) (hprob : ∀ ρ ∈ P, Probability ρ) (hε : 0 < ε)
    (hsuper : ∀ ρ ∈ P, ε ≤ conflictMass ρ H) :
    ∃ law : Finset U → U → ℝ, ∃ pick : Finset U → U,
      ∀ R, (residual P R).Nonempty →
        law R ∈ residual P R ∧
        (∀ σ ∈ residual P R, entropy (law R) q ≤ entropy σ q) ∧
        pick R ∈ R ∧ ε ≤ neighborMass (law R) H (pick R) ∧
        (∃ w ∈ R, H (pick R) w) := by
  classical
  have hall : ∀ R : Finset U, ∃ ρ : U → ℝ, ∃ v : U,
      (residual P R).Nonempty →
        ρ ∈ residual P R ∧ (∀ σ ∈ residual P R, entropy ρ q ≤ entropy σ q) ∧
        v ∈ R ∧ ε ≤ neighborMass ρ H v ∧ (∃ w ∈ R, H v w) := by
    intro R
    by_cases ha : (residual P R).Nonempty
    · obtain ⟨ρ,hρ,hmin⟩ := Lax342547.RelativeEntropy.compact_entropy_minimizer
        (residual P R) q (Lax342547.ContainerLaws.residual_compact P R hc) ha
      obtain ⟨v,hv,hm⟩ := Lax342547.ContainerLaws.heavy_neighbor
        ρ H R ε (hprob ρ hρ.1) hρ.2 hε (hsuper ρ hρ.1)
      exact ⟨ρ,v,fun _ => ⟨hρ,hmin,hv,hm,Lax342547.EntropySelectors.heavy_neighbor_nonempty ρ R H v hρ.2 (hε.trans_le hm)⟩⟩
    · exact ⟨fun _ => 0,Classical.choice inferInstance,fun h => (ha h).elim⟩
  choose law pick hspec using hall
  exact ⟨law,pick,hspec⟩

end Lax342547Proofs.EntropySelectors
