import Lax342547.CoverCounts
import Lax342547Proofs.SmallExposure

namespace Lax342547Proofs.CoverCounts
open Lax342547.CoverCounts

set_option backward.isDefEq.respectTransparency false

/--
---
conclusion: Lax342547.CoverCounts.covered_count_lower_bound
---
-/
theorem covered_count_lower_bound {ι : Type} (I : Finset ι) (P : ι → Prop)
    (b t : ℕ) (rank d : ℝ) (hI : I.card = b) (hbt : 2*t ≤ b)
    (hr : rank < (t : ℝ)/4) (hd : d < (b : ℝ)/4)
    (hc : by classical exact ((I.filter P).card : ℝ) ≤ rank+d) : by
      classical
      exact t ≤ (I.filter (fun i => ¬ P i)).card := by
  classical
  have hh := Finset.card_filter_add_card_filter_not (s := I) P
  rw [hI] at hh
  have hh' : ((I.filter P).card : ℝ)+(I.filter (fun i => ¬ P i)).card = b := by exact_mod_cast hh
  have hbt' : 2*(t : ℝ) ≤ b := by exact_mod_cast hbt
  have hn : (t : ℝ) ≤ (I.filter (fun i => ¬ P i)).card := by linarith
  exact_mod_cast hn

end Lax342547Proofs.CoverCounts
