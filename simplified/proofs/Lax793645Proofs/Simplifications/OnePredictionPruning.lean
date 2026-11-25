/- Exactification and finite prediction-class selection for the
one-frame law. The finite trimming proof follows the vendored
Apache-2.0 PredictionDichotomy argument. -/
import Lax793645Proofs.Simplifications.OnePreparationBounds
import Lax793645Proofs.Simplifications.OnePredictionCohorts

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open PreparationParameters PredictionClass Filter Finset Matrix
open scoped BigOperators Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {M n N : ℕ} {q : PreparationParameters} {m : cycleM p}
  {s : OneRhythms p M} {w : OneTale p M} {b : OneSketch p M}
  {U : Ultrafilter ℕ} {P : OneCampaign p M}

set_option maxHeartbeats 1800000 in
theorem one_prune_whisper (hl : (U:Filter ℕ)≤atTop) (hq : OnePlanted q p M)
    (hw : ∀ᶠ n in U,OneNascent q (m n) (w n))
    (hx : ∀ᶠ n in U,OneEntered q (m n) (w n) (s n))
    (hc : b.c=dusk)
    (hf : OneLedger b (U:Filter ℕ))
    (hg : ∀ i,∃ r, oneDisappearing U (b.g i) r)
    (h : ∀ᶠ n in U, crowdSeed ≤ pr ((s n).sap (w n)) (P n) ∧
       ∀ x,P n x → oneSeems q (m n) (s n) x (fun i=>b.g i n) (b.m n x) (b.L n x) b.α (b.ε n)) :
    ∃ Q:OneCampaign p M,∀ᶠ n in U, pollen ≤ pr ((s n).sap (w n)) (Q n) ∧
       ∀ x,Q n x→P n x∧oneExactInk (m n) (b.m n) x := by
  classical
  have ha : ∀ i,b.α i=1 := dusk_lit _ (hc ▸ hf.light)
  choose g hG using hg
  let Y (n) (x : OneUnit p n (M*n)) i := oneWhisper p (b.g i n) (g i) (x i)
  let Q : OneCampaign p M := fun n x=>P n x∧∀ i,Y n x i
  have he :
      ∀ᶠ n in U,∀ (i : Bool) (l : Tag p.g) (b':F),oneTabRef p l b' (b.g i n) (g i) ≤1/100 :=
    eventually_all.mpr fun i=> eventually_all.mpr fun l=> eventually_all.mpr fun b'=> hG i l b'
      _ (by norm_num)
  have hz :
      ∀ᶠ n : ℕ in atTop, (2:ℝ)*(2*q.L*bp (-(1/16:ℝ)*n))≤pollen := by
    have hh : Tendsto (fun n:ℕ=>(2:ℝ)*(2*q.L*bp (-(1/16:ℝ)*n))) atTop (𝓝 0) := by
      have h := ((bp_nat_vanish (by norm_num : 0<(1/16:ℝ))).const_mul (2*q.L)).const_mul 2
      simpa using h
    exact (hh.eventually (gt_mem_nhds pollen_pos)).mono (fun _ hi=>hi.le)
  refine ⟨Q,?_⟩
  filter_upwards [hw,hx,h,hq.unary_room.filter_mono hl,he,hf.small (1/16) (by norm_num),
    (one_hush_calendar p M hq.hM hq.hG hq.hR hq.hJ).filter_mono hl,hz.filter_mono hl,
    (eventually_ge_atTop (2*p.r)).filter_mono hl] with n hn ht hs hq' hG hε hh hz hN
  let s':=s n; let w':=w n
  let v:=s'.sap w'
  have hv : IsLaw v:= ImageLeafMixture.sap_law (lt_of_lt_of_le (by norm_num) ht.weight) hn.law
  have hS : oneBySide v (m n) (2*q.L) := by
    refine one_upper_side hn.border (H:=2) (fun x=>?_) (by norm_num) le_rfl
    exact (on_mon hn.law.nz (by norm_num) ht.weight x).trans_eq (by norm_num)
  constructor
  · let V (x : OneUnit p n (M*n)) := ∀ i,Y n x i
    have hT := pr_shield hv.nz (P n) V
    let δ := 2*q.L*bp (-(1/16:ℝ)*n)
    have hi (i:Bool) : pr v (fun x=>¬Y n x i) ≤ δ := by
      let T (o:OneOrient p n (M*n)) := ¬ oneWhisper p (b.g i n) (g i) o
      let f (x : OneUnit p n (M*n)):= x i
      change pr v (fun x=>T (f x)) ≤ _
      rw [←mapW_pr]
      apply (pr_cap (hS i) T).trans
      exact mul_le_mul_of_nonneg_left (hh (m n) hq' _ _ (hG i))
        (mul_nonneg (by norm_num) hq.early.hL)
    have hf : pr v (fun x=>¬V x)≤pollen := by
      refine le_trans ?_ hz
      calc pr v (fun x=>¬V x)
        _ ≤ ∑ i:Bool,pr v (fun x=>¬Y n x i) :=
          (pr_mono hv.nz (p:=fun x=>¬V x) (fun x h => show ∃ i:Bool,¬Y n x i from not_forall.mp h)).trans
            (pr_exists_le hv.nz _)
        _ ≤ 2*δ := by rw [Fintype.sum_bool,two_mul]; exact add_le_add (hi _) (hi _)
    have hh : 2*pollen ≤ pr v (P n) := hs.1
    exact le_trans (by linarith only [hh,hf]) hT
  · intro x hh
    have hs := hs.2 x hh.1
    refine ⟨hh.1,fun i=>?_⟩
    have hi :
        onePostulates (x i) (b.g i n) (oneYoke (m n) x i (b.m n x i) 1) (b.L n x i) (1/16) := by
      rw [←ha i]
      exact fun z hz j k=>(hs.2 i z hz j k).trans hε
    have he : (↑(b.L n x i).card:ℝ)<bp ((p.b:ℝ)-2*p.j) :=
      lt_of_le_of_lt (by exact_mod_cast (hs.1 i).1) hq.hB
    exact (one_hush_vat _ _ _ _ (g i) he hi (hh.2 i) hq.hg hq.hR hN).2

end
end Lax793645Proofs.Simplifications
