/-
Adapted from OpenAI, openai/math, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a (Apache-2.0).
Changes: Lax package separation, namespaces, explicit variables, and archive annotations.
-/
import Lax342547.CliqueMinor
import Lax342547.MatchingMinorBound
import Lax342547Proofs.HadwigerMatching.SmallBranches
import Lax342547Proofs.HadwigerMatching.BranchGeometry
import Lax342547Proofs.HadwigerMatching.PairingExtension
import Lax342547Proofs.HadwigerMatching.BasicMatching

namespace Lax342547Proofs

/-! The integral Hadwiger bound from pairwise touching matchings.

The small-branch counting argument is Proposition `matching-minor` of
*A counterexample to Hadwiger's conjecture*, following the connected-matching
approach of Cambie.
-/

open Lax342547.ConnectedMatching Lax342547.CliqueMinor

namespace HadwigerMatching

variable {V : Type} [Fintype V] {G : SimpleGraph V}

/-- The singleton and doubleton deficits of an actual clique-minor model are
controlled by a touching matching constructed from those very branches. -/
theorem small_branch_deficit_le {t : ℕ} (B : Fin t → Finset V)
    (hconn : ∀ i, (G.induce (B i : Set V)).Connected)
    (hne : ∀ i, (B i).Nonempty)
    (hdisj : Pairwise (fun i j => Disjoint (B i) (B j)))
    (htouch : ∀ i j, i ≠ j → ∃ v ∈ B i, ∃ w ∈ B j, G.Adj v w) :
    2 * singletonBranchCount B + doubletonBranchCount B ≤
      4 * connectedMatchingNumber G + 2 := by
  classical
  have hE := twoVertexBranches_isTouchingMatching G B hdisj htouch
    (fun i hi => connected_card_two_isClique (B i) hi (hconn i))
  obtain ⟨P, hP, hcard, hcover⟩ := extend_matching_by_clique_pairs G
    (twoVertexBranches B) (singletonVertices B) hE
    (singletonVertices_isClique G B htouch)
    (fun _ he => twoVertexBranches_disjoint_singletonVertices B hdisj he)
    (fun _ hv _ he => singletonVertices_touch_twoVertexBranches G B htouch hv he)
  have hbound := matching_card_le_number hP
  rw [hcard, card_twoVertexBranches B hne hdisj] at hbound
  rw [card_singletonVertices B hdisj] at hcover
  omega

/-- Every clique minor satisfies the integral matching bound. -/
theorem clique_minor_matching_bound {t : ℕ}
    (h : HasCliqueMinor G t) :
    3 * t ≤ Fintype.card V + 4 * connectedMatchingNumber G + 2 := by
  classical
  obtain ⟨B, hconn, hne, hdisj, htouch⟩ := finite_branch_model h
  have hcount := branch_counting B hne hdisj
  have hsmall := small_branch_deficit_le B hconn hne hdisj htouch
  omega

/--
---
conclusion: Lax342547.MatchingMinorBound.hadwiger_matching_bound
---
The maximum is attained by an actual clique-minor branch model. This proves
the bound for the literal Hadwiger number, including the empty graph. -/
theorem hadwiger_matching_bound (G : SimpleGraph V) :
    3 * hadwigerNumber G ≤
      Fintype.card V + 4 * connectedMatchingNumber G + 2 :=
  clique_minor_matching_bound (Lax342547Proofs.CliqueMinor.hasCliqueMinor_hadwigerNumber G)

end HadwigerMatching

end Lax342547Proofs
