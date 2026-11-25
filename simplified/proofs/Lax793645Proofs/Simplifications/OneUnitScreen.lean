import Lax793645Proofs.Simplifications.OneCommonImageRanks
import Lax793645Proofs.Simplifications.OneZeroDiscrepancyPrediction
import Lax793645Proofs.Simplifications.CycleMarkedProfiles

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix Finset Function Filter Real
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N : ℕ}

set_option maxHeartbeats 1200000 in
theorem one_unit_screen (p : Shape)
    (K D q B : ℕ)
    (hD : (p.g-1)/2+2*D≤q) (h3 : 3≤p.g)
    (hB : B < Fintype.card (Label p.b))
    (m : Mixer p n) (x : OneUnit p n N)
    (hg' : Odd p.g) (hj : 1≤p.j)
    (v : Bool → Profile p n) (α : Bool → F) (ha : α true≠α false)
    (hy : ∀ i, v i ∈ Xspace p n ∧ totalRank (v i) ≤ K ∧ oneFrameLaw m (x i))
    (hz : oneJoins x ≤2*D) (h : oneMomentEmbed (x true) (v true)=oneMomentEmbed (x false) (v false))
    (L : Bool→ Finset (Label p.b)) (hL : ∀ i,(L i).card≤B)
    (g : Bool→OneAugur p N) (ε : ℝ)
    (he : oneClaimed x g m v α L ε) :
    ∃ (s : Label p.b) (E : Finset (Tag p.g)), E.card≤ q ∧ ∃ b,
      oneScreen p (x b) s E (oneScreenRank p K) (g b) ε := by
  classical
  have hxA : oneFrameLaw m (x true) := (hy true).2.2
  have hxB : oneFrameLaw m (x false) := (hy false).2.2
  obtain ⟨h1,h2⟩:=one_total_rank_shared x m (fun i=>(hy i).2.2) h
  have ht (i:Bool) : totalRank (v i) ≤2*D := by
    cases i
    · rw [←h1]; exact h2.trans hz
    exact h2.trans hz
  choose τ hτ htrace using fun i : Bool => exists_majority_trace (v i) (hy i).1 hg'
  have hP : τ true=τ false := majority_trace_unique hg' h3 _ _ (hτ true) (hτ false) (by
    intro e
    rw [←htrace true e,←htrace false e,←one_common_image_tester hj hxA hxB (hy true).1 (hy false).1 h e])
  obtain ⟨b,hb⟩ : ∃ b,(∑ t,τ b t)+α b=1 := by
    by_contra! hv
    have hz (i:Bool) : (∑ t,τ i t)+α i=0 := (bit_cases _).resolve_right (hv i)
    have hx := hz true
    rw [hP] at hx
    exact ha (add_left_cancel (hx.trans (hz false).symm))
  obtain ⟨s,hf⟩ : ∃ s,s∉L b := by
    by_contra! h
    have hz : univ ⊆ L b := fun i _=>h i
    have hh := (card_le_card hz).trans (hL b); rw [card_univ] at hh; omega
  let E := bitSupport (fun t => τ b t+ordinaryBit p n (v b) t)
  have hE : E.card≤q := (sharedBit_support hg' h3 D (v b) (τ b) (hτ b) (ht b)).trans hD
  refine ⟨s,E,hE,b,?_⟩
  apply one_zero_screen p x b s m (α b) hg' (v b) E ?_ K (hy b).2.1 _ ε (L b) hf (he b)
  intro t htE
  have hz : τ b t+ordinaryBit p n (v b) t=0 := by
    by_contra h
    exact htE (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
  rw [intrinsic_tester (v b) (hy b).1 hg' (τ b) (htrace b) t,hz,add_zero]
  exact hb

end
end Lax793645Proofs.Simplifications
