/- The finite four-bit phase calculation, adapted from the vendored
Apache-2.0 FourPhaseBits proof to the actual one-frame listeners. -/
import Lax793645Proofs.Simplifications.OneCoverRecords

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix Module Finset
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N : ℕ}

theorem one_tone_vec (x : OneUnit p n N) (S : Party) (Δ : Ambient p (2*N)) :
    joinPhase p (oneListens x) S Δ=
      dotProduct S (fun i=>joinPhase p (oneListens x) (unary i) Δ) := by
  classical
  have hg (i) : joinPhase p (oneListens x) (unary i) Δ=uPhase p (onSide (oneListens x) i) Δ := by
    unfold joinPhase unary
    rw [Finset.sum_eq_single i]
    · rw [Pi.single_eq_same,one_smul]
    · intro j _ hj; simp [hj]
    simp
  unfold dotProduct
  simp_rw [hg]
  unfold joinPhase
  simp

private theorem quad_rate (x : Quad) : unif x=(1:ℝ)/16 := by
  rw [unif_apply,quad_card]; norm_num

private theorem joint_phase (p : Shape) {n N} (Δ : OneUnit p n N→ Ambient p (2*N)) (x) (S) :
    quadPhase S (oneQuench Δ x) = oneChant Δ S.1 S.2 x := by
  unfold quadPhase oneChant
  unfold quadDot oneQuench
  dsimp only
  rw [←one_tone_vec, ←one_tone_vec,add_comm]

theorem one_quad_invert (p : Shape) {n N} (Δ : OneUnit p n N→Ambient p (2*N)) (w) (s : Quad) :
    pr (pairW w w) (fun x => oneQuench Δ x=s)=
    avg unif (fun v : Quad => channelPitch Δ oneListens w v.1 v.2 * quadPhase v s) := by
  unfold pr
  simp_rw [quad_inv, joint_phase]
  rw [avg_avg]
  simp_rw [avg_mul]
  rfl

theorem one_mix_pattern (p : Shape) {n N} (Δ : OneUnit p n N→Ambient p (2*N)) (w)
    (hw : IsLaw w) (h : oneTonalMix Δ w) (s : Quad) :
    0.05 < pr (pairW w w) (fun x => oneQuench Δ x=s) := by
  classical
  rw [one_quad_invert]
  let f := fun S : Quad => ind (S=0) - 0.005
  have hf S : f S≤channelPitch Δ oneListens w S.1 S.2*quadPhase S s := by
    by_cases hS : S=0
    · have h0 : channelPitch Δ oneListens w 0 0=1 := by
        unfold channelPitch
        have hz (x : OneUnit p n N) y : joinPhase p (oneListens x) 0 (Δ y)=0 := by rw [one_tone_vec,zero_dotProduct]
        simp_rw [hz,add_zero, wsign_zero]; exact (pairW_law hw hw).avg_const _
      rw [hS]
      change f 0≤channelPitch Δ oneListens w 0 0*quadPhase 0 s
      rw [h0]
      norm_num [f,quadPhase,quadDot]
    · have hh := h _ _ (show S.1≠0 ∨ S.2≠0 from by
        by_contra! he; exact hS (Prod.ext he.1 he.2))
      have he : |channelPitch Δ oneListens w S.1 S.2*quadPhase S s| < 0.005 := by rwa [abs_mul,quadPhase,wsign_abs,mul_one]
      simpa only [f,ind_zero hS,zero_sub] using (abs_lt.mp he).1.le
  apply lt_of_lt_of_le _ (avg_mono unif_law.nz hf)
  unfold f; rw [avg_sub, unif_law.avg_const]
  change 0.05 < pr unif (fun S : Quad => S=0)-0.005
  rw [pr_point',quad_rate]; norm_num

private theorem party_single (x : Party) (h : x∉evenP) : ∃ i,x=unary i := by
  classical
  rcases bit_cases (x true) with a|a <;> rcases bit_cases (x false) with b|b
  · have he : x=0 := funext fun i => by cases i; exact b; exact a
    simp [he,evenP] at h
  · refine ⟨false,funext fun i => ?_⟩; cases i <;> simp [a,b,unary]
  · refine ⟨true,funext fun i => ?_⟩; cases i <;> simp [a,b,unary]
  have he : x=allSide := funext fun i => by cases i; exact b; exact a
  simp [he,evenP] at h

private theorem even_dot (_ : Quad) (v : Quad) (h : v∈evenQ) (j : F) :
    quadPhase v (repeatQ j)=1 := by
  classical
  have he (b : Party) (h : b∈evenP) : dotProduct b (fun _ => j)=0 := by
    have h : b=0 ∨ b=allSide := by simpa [evenP] using h
    rcases h with h|h
    · rw [h,zero_dotProduct]
    simp only [h,dotProduct,Fintype.sum_bool,allSide,one_mul,char_two]
  obtain ⟨ha,hb⟩ := Finset.mem_product.mp h
  unfold quadPhase quadDot repeatQ
  dsimp only
  rw [he _ ha,he _ hb]; simp

private theorem even_sum (x : Quad) (i : F) :
    ∑ v∈evenQ,quadPhase v x*quadPhase v (repeatQ i)=4*ind (repeated x) := by
  classical
  let f (x : Party) (v : Party) := wsign (dotProduct v x)
  have hh (x) :
      ∑ v∈evenP,f x v=2*ind (dotProduct allSide x=0) := by
    have hn : allSide≠0 := by
      intro e
      have hh := congr_fun e true
      change (1:F)=0 at hh; simp at hh
    simp only [evenP,Finset.sum_insert (show (0:Party)∉ ({allSide}:Finset _) from
      fun h => hn (mem_singleton.mp h).symm),Finset.sum_singleton,f, zero_dotProduct, wsign_zero]
    by_cases ht : dotProduct allSide x=0
    · norm_num [ind,ht]
    norm_num [ind,ht,wsign]
  have ht (v : Quad) (h : v∈evenQ) : quadPhase v x * quadPhase v (repeatQ i)
      = f x.1 v.1 * f x.2 v.2 := by
    rw [even_dot x _ h,mul_one,quadPhase,quadDot,wsign_add]
  rw [Finset.sum_congr (g:=fun v => f x.1 v.1 * f x.2 v.2) rfl ht,evenQ, Finset.sum_product]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul,hh,hh,repeated,ind_and]; ring

set_option maxHeartbeats 800000 in
theorem one_tiny_pattern (p : Shape) {n N} (Δ : OneUnit p n N→Ambient p (2*N)) (w)
    (i : F) {h : ℝ} (h0 : 0≤h)
    (hw : ∀ i : Bool,∀ R, |channelPitch Δ oneListens w (unary i) R|≤h) :
    (1/4:ℝ)*pr (pairW w w) (fun x => repeated (oneQuench Δ x))-h ≤
      pr (pairW w w) (fun x => oneQuench Δ x=repeatQ i) := by
  classical
  let f (v : Quad) := channelPitch Δ oneListens w v.1 v.2*quadPhase v (repeatQ i)
  let μ := pairW w w
  let g (S : Quad) := ind (S∈evenQ)*f S
  have he (x : Quad) : g x - h ≤ f x := by
    by_cases hx : x∈evenQ
    · unfold g; rw [ind_one hx,one_mul]
      exact sub_le_self _ h0
    have hi : |channelPitch Δ oneListens w x.1 x.2|≤h := by
      by_cases he : x.1∈evenP
      · obtain ⟨i,hit⟩ := party_single x.2 (fun hh => hx (Finset.mem_product.mpr ⟨he,hh⟩))
        rw [hit,one_pitch_turn]
        exact hw i _
      obtain ⟨i,hi⟩ := party_single _ he
      rw [hi]; exact hw i _
    have hs : |f x|≤h := by unfold f quadPhase; rwa [abs_mul,wsign_abs,mul_one]
    unfold g; rw [ind_zero hx,zero_mul,zero_sub]
    exact (abs_le.mp hs).1
  have hg : avg unif g=(1/4:ℝ)*pr μ (fun x => repeated (oneQuench Δ x)) := by
    have ht : ∑ x : Quad,g x= ∑ x∈evenQ,f x := by
      symm
      simp only [g,ind,ite_mul,one_mul,zero_mul,← Finset.sum_filter]
      simp
    have hB (x : Quad) :
        f x=avg μ (fun y => quadPhase x (oneQuench Δ y)*quadPhase x (repeatQ i)) := by
      rw [avg_mul]; simp_rw [joint_phase]; rfl
    have hf : ∑ x∈evenQ,f x=4*pr μ (fun x => repeated (oneQuench Δ x)) := by
      simp_rw [hB,← avg_sum,even_sum,avg_mul']; rfl
    simp only [avg,quad_rate,← Finset.mul_sum, ht,hf]
    unfold pr avg
    ring
  rw [one_quad_invert,show _*pr _ _=_ from hg.symm]
  calc avg unif g - h = avg unif (fun x => g x-h) := by rw [avg_sub,unif_law.avg_const]
       _ ≤ _ := avg_mono unif_law.nz he

end
end Lax793645Proofs.Simplifications
