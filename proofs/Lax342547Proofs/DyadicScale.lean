import Lax342547.DyadicScale
import Lax342547.DyadicDeficits
import Lax342547.DyadicTails

namespace Lax342547Proofs.DyadicScale
open Lax342547.DyadicScale

set_option backward.isDefEq.respectTransparency false
open Lax342547.DyadicTails
open scoped BigOperators

/--
---
conclusion: Lax342547.DyadicScale.single_scale
---
-/
theorem single_scale (f v : ℕ → ℝ) (n : ℕ) (r : ℝ)
    (hrec : ∀ j < n, 2*v j ≤ 2*(f j-f (j+1))+v (j+1))
    (hf0 : f 0 ≤ r) (hfn : 0 ≤ f n) (hv0 : 0 ≤ v 0) (hvn : v n ≤ f n)
    (hn : 8*r < n) : ∃ j < n, v j < 1/4 := by
  have hs := Lax342547.DyadicDeficits.deficit_ratio_sum f v n r hrec hf0 hfn hv0 hvn
  by_contra hh
  push Not at hh
  have hsum : (n : ℝ)*(1/4) ≤ ∑ j ∈ Finset.range n, v j := by
    calc
      _ = ∑ j ∈ Finset.range n, (1/4 : ℝ) := by simp [nsmul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum (fun j hj => hh j (Finset.mem_range.mp hj))
  linarith

/--
---
conclusion: Lax342547.DyadicScale.dyadic_small_tail
---
-/
theorem dyadic_small_tail (a : ℕ → ℝ) (ha : Antitone a) (ha0 : ∀ t, 0 ≤ a t)
    (k n : ℕ) (r : ℝ) (hnk : n ≤ k) (har : a 0 ≤ r) (hn : 8*r < n) :
    ∃ j < n, tailDeficit a (2^k) (2^(k-j)) < 1/4 := by
  let f : ℕ → ℝ := fun j => a (2^k-2^(k-j))
  let v : ℕ → ℝ := fun j => tailDeficit a (2^k) (2^(k-j))
  apply Lax342547.DyadicScale.single_scale f v n r _ _ _ _ _ hn
  · intro j hj
    have hjk : j+1 ≤ k := by omega
    have hpow : 2*2^(k-(j+1)) = (2 : ℕ)^(k-j) := by
      rw [show k-j=(k-(j+1))+1 by omega,pow_succ]
      omega
    have hbs : 2*2^(k-(j+1)) ≤ (2 : ℕ)^k := by
      rw [hpow]
      exact Nat.pow_le_pow_right (by omega) (Nat.sub_le _ _)
    have hh := Lax342547.DyadicTails.dyadic_recurrence a ha (2^k) (2^(k-(j+1))) (by positivity) hbs
    simpa only [hpow,f,v] using hh
  · simpa [f] using har
  · exact ha0 _
  · exact Lax342547.DyadicTails.tail_deficit_nonneg a ha _ _ (by positivity)
  · exact Lax342547.DyadicTails.tail_deficit_le a ha0 _ _

end Lax342547Proofs.DyadicScale
