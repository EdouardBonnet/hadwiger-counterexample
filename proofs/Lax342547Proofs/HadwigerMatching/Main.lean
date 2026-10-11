/-
Adapted from OpenAI, openai/math, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a (Apache-2.0).
Changes: Lax package separation, namespaces, explicit variables, and archive annotations.
-/
import Lax342547.CliqueMinor
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Lax342547.ChromaticBound
import Lax342547.MatchingMinorBound

namespace Lax342547Proofs

open Lax342547.ConnectedMatching Lax342547.CliqueMinor

namespace HadwigerMatching

/-- The matching–minor proposition: the Hadwiger bound and its chromatic
consequence when the independence and touching-matching numbers are small. -/
theorem full_matching_minor_proposition
    (V : Type) [Fintype V] [Nonempty V] (G : SimpleGraph V) :
    let m : ℕ := Fintype.card V
    let h : ℕ := hadwigerNumber G
    let c : ℕ := connectedMatchingNumber G
    (h : ℚ) ≤ ((m : ℚ) + 4 * (c : ℚ) + 2) / 3 ∧
      (G.indepNum ≤ 2 →
        (c : ℚ) < (m : ℚ) / 100 →
        5 ≤ m →
        (h : ℚ) < 26 * (m : ℚ) / 75 + 2 / 3 ∧
        26 * (m : ℚ) / 75 + 2 / 3 < (m : ℚ) / 2 ∧
        (m : ℚ) / 2 ≤ (G.chromaticNumber.toNat : ℚ)) := by
  dsimp only
  have hn := Lax342547.MatchingMinorBound.hadwiger_matching_bound G
  have hq : 3 * (hadwigerNumber G : ℚ) ≤
      (Fintype.card V : ℚ) + 4 * (connectedMatchingNumber G : ℚ) + 2 := by
    exact_mod_cast hn
  refine ⟨by linarith, ?_⟩
  intro hα hc hm
  have hm' : (5 : ℚ) ≤ (Fintype.card V : ℚ) := by exact_mod_cast hm
  have hnχ := Lax342547.ChromaticBound.card_le_twice_chromaticNumber_of_indepNum G hα
  have hχ : (Fintype.card V : ℚ) ≤ 2 * (G.chromaticNumber.toNat : ℚ) := by
    exact_mod_cast hnχ
  refine ⟨?_, ?_, ?_⟩ <;> linarith

end HadwigerMatching

end Lax342547Proofs
