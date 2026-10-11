import Lax342547.SmallExposure
import Lax342547.CombinedSpans
import Lax342547.GreedySpans
import Lax342547.GreedyTails

namespace Lax342547Proofs.SmallExposure
open Lax342547.SmallExposure

set_option backward.isDefEq.respectTransparency false
open Lax342547.GreedySpans Lax342547.GreedyTails
open scoped BigOperators

/--
---
conclusion: Lax342547.SmallExposure.simultaneous_small_exposure
---
-/
theorem simultaneous_small_exposure {K V W ι : Type} [Field K] [Fintype ι] [DecidableEq ι]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [FiniteDimensional K V] [FiniteDimensional K W]
    (C : ι → Submodule K V) (R : ι → Submodule K W) (r : ℝ) (k n : ℕ)
    (hC : ∀ i, (Module.finrank K (C i) : ℝ) ≤ r)
    (hR : ∀ i, (Module.finrank K (R i) : ℝ) ≤ r)
    (hcard : Fintype.card ι = 2^k) (hnk : n ≤ k) (hn : 16*r < n) :
    ∃ l : List ι, l.Nodup ∧ l.toFinset = Finset.univ ∧ ∃ j < n,
      deficit C (spanAfter C ⊥ (l.take (l.length-2^(k-j)))) (l.drop (l.length-2^(k-j)))+
      deficit R (spanAfter R ⊥ (l.take (l.length-2^(k-j)))) (l.drop (l.length-2^(k-j))) <
        (2^(k-j) : ℝ)/4 := by
  obtain ⟨l,hl,hI,hg⟩ := Lax342547.GreedySpans.exists_greedy_order
    (fun i => (C i).prod (R i)) Finset.univ ((⊥ : Submodule K V).prod (⊥ : Submodule K W))
  have hlen : l.length = 2^k := by
    rw [← List.toFinset_card_of_nodup hl,hI,Finset.card_univ,hcard]
  have hr : ∀ i ∈ l, (Module.finrank K ((C i).prod (R i)) : ℝ) ≤ 2*r := by
    intro i _
    rw [Lax342547.CombinedSpans.product_space_dimension]
    push_cast
    linarith [hC i,hR i]
  obtain ⟨j,hj,hd⟩ := Lax342547.GreedyTails.small_greedy_tail
    (fun i => (C i).prod (R i)) ((⊥ : Submodule K V).prod (⊥ : Submodule K W))
    l hg (2*r) hr k n hlen hnk (by linarith)
  rw [Lax342547.CombinedSpans.span_after_product,Lax342547.CombinedSpans.deficit_product] at hd
  exact ⟨l,hl,hI,j,hj,hd⟩

end Lax342547Proofs.SmallExposure
