import Lax793645Proofs.Simplifications.ReducedPolarBounds
import Lax793645Proofs.Simplifications.ReducedExplicitMixers

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix Filter
open scoped BigOperators Topology Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem reduced_polar_likely (p : Shape) (K s0 : ℕ) (hA : profileA p K≤s0)
    (hg : 3≤p.g) (hodd : Odd p.g) (hj : s0≤p.J) :
    ∀ᶠ n : ℕ in atTop,
      pr unif (fun x : ReducedDraw p n => ¬unaryGood (reducedMixer x) K s0)<1/4 := by
  classical
  let A := profileA p K
  let U := Tag p.g × Label p.b
  let c : ℝ := (reducedProdBound p K+2*reducedRankBudget p K:ℕ)
  let b := num U * bp (c*(s0+1))
  have h : Tendsto (fun n:ℕ => b*bp (-(n:ℝ))) atTop (𝓝 0) := by
    have h : Tendsto (fun n:ℕ=>bp (-(1:ℝ)*(n:ℝ))) atTop (𝓝 0) :=
      (bp_tendsto_zero zero_lt_one).comp tendsto_natCast_atTop_atTop
    simpa using h.const_mul b
  filter_upwards [h.eventually (gt_mem_nhds (show (0:ℝ)<1/4 by norm_num)),profile_count p K]
    with n hn hP
  let T := {x : Profile p n // totalRank x≤K}
  let bad (i : T × U) (d : ReducedDraw p n) := reducedUrBad K s0 i.1.val i.2.1 i.2.2 d
  apply lt_of_le_of_lt (le_trans (pr_mono unif_law.nz ?_) (pr_exists_le _ bad))
  show (∑ i,pr unif (bad i)) < 1/4
  · have hi i : pr unif (bad i) ≤ bp ((c-n)*(s0+1)) := by
      have hi := reducedUrBad_cap K s0 hg hodd hj (i: T × U).1.val i.2.1 i.2.2
      unfold c; push_cast; exact hi
    apply lt_of_le_of_lt (Finset.sum_le_sum (s:=Finset.univ) fun i _ => hi i)
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    apply lt_of_le_of_lt _ hn
    change _ ≤ b * bp _
    have hpc : num T ≤ bp (A*n) := by rw [nbr_eq_card] at hP; exact hP
    rw [Fintype.card_prod,Nat.cast_mul]
    change num T * num U * _ ≤ _
    have hh : (A:ℝ)*n - (s0+1:ℝ)*n ≤ -(n:ℝ) := by
      have hx : (A:ℝ) ≤ s0 := by exact_mod_cast hA
      have hd := mul_le_mul_of_nonneg_right hx (Nat.cast_nonneg n : (0:ℝ) ≤ n)
      linarith only [hd]
    have hnum : (0:ℝ) ≤ num U := Nat.cast_nonneg _
    calc num T * num U * bp ((c-n)*(s0+1))
      _ ≤ bp (A*n) * num U * bp ((c-n)*(s0+1)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpc hnum) (bp_pos _).le
      _ = b * bp ((A:ℝ)*n - (s0+1:ℝ)*n) := by
        dsimp only [b]
        rw [mul_comm _ (num U),mul_assoc, ← bp_add, mul_assoc, ← bp_add]; ring_nf
      _ ≤ _ := mul_le_mul_of_nonneg_left (bp_le hh) (mul_nonneg hnum (bp_pos _).le)
  · intro x hx
    unfold unaryGood at hx
    push Not at hx
    obtain ⟨i,l,s,h1,h2,h3⟩ := hx
    exact ⟨(⟨i,h1⟩,l,s),h1,h2,h3⟩
  · exact unif_law.nz;

theorem goodReducedMixers (p : Shape) (K s0 : ℕ) (hg : 3≤p.g) (hodd : Odd p.g)
    (hj : 1≤p.j) (h0 : profileA p K≤s0) (hJ : s0≤p.J) :
    ∀ᶠ n : ℕ in atTop,∃ m : Mixer p n,unaryGood m K s0 ∧ reducedBinaryGood m := by
  filter_upwards [reduced_polar_likely p K s0 h0 hg hodd hJ,
    eventually_ge_atTop (4*(reducedMixerCount p+p.b)+4)] with n hn hsize
  let q (x : ReducedDraw p n):=¬unaryGood (reducedMixer x) K s0
  have hh:0<pr unif (fun x=>¬q x) := by
    rw [pr_not,unif_law.total]
    change pr unif q<_ at hn
    linarith only [hn]
  obtain ⟨x,hx,_⟩:=exists_of_pr_pos unif_law.nz hh
  have hu:unaryGood (reducedMixer x) K s0:=Classical.not_not.mp hx
  exact ⟨reducedMixer (explicitReduced x),explicitReduced_unary x K s0 hu,
    reduced_mixer_law hg _,explicitReduced_binary_rank x hg hj hsize⟩

end
end Lax793645Proofs.Simplifications
