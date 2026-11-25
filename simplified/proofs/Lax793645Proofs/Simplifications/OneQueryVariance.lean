import Lax793645Proofs.Simplifications.OneBatchIndependence
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.QueryConcentration

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function LinearMap
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I G A : Type} [Fintype I] [Fintype G] [Fintype A]
  [DecidableEq I] [DecidableEq G] {p : Shape} {n N : ℕ}
variable {g : Route I G} {s : Program p n g A}

def oneOexpect (s : Program p n g A) (w : Wgt A) (T : A→Rack I N→ℝ)
    (o : OneForum p n N G) := avg w (fun x=>T x (onePeek g (s.left x) o))

theorem one_forum_law (m : Mixer p n)
    (hN : Fintype.card (Row p n)+2*p.h+1≤N) : IsLaw (oneForumLaw (G:=G) m N) := by
  apply prodW_law
  intro c
  exact quadratic_channel_raw_law _ (hyperbolic_matrix_nondegenerate N) _
    (one_frame_room hN)

set_option maxHeartbeats 800000 in
theorem one_oVar (m : Mixer p n) (hN : Fintype.card (Row p n)+2*p.h+3≤N)
    (T : A→Wgt (Rack I N))
    (w : Wgt A) (hw : IsLaw w) (hT : ∀ i x,|T i x|≤1)
    (k : ℝ) (hk : ∀ i,num (Port (tied g Bool) i)≤k)
    (hK : 2*k+2≤(N:ℝ))
    (r : ℝ) (hr : pr (draws Bool w) (fun x => ¬ s.free x) ≤ r) :
    let v := oneForumLaw (G:=G) m N
    let f := oneOexpect s w T
    avg v (fun o => (f o-avg v f)^2) ≤
      2*r + 2*quadraticNetFact (tied g Bool)*twinkle (tied g Bool) k N := by
  classical
  let v := oneForumLaw (G:=G) m N
  let f := oneOexpect s w T
  let F (x : A) := fun o => T x (onePeek g (s.left x) o)
  let D := draws Bool w
  let B := 2*quadraticNetFact (tied g Bool)*twinkle (tied g Bool) k N
  have hD : IsLaw D := draws_law hw
  have hv : IsLaw v := one_forum_law _ (by omega)
  let V (x : Bool→A) := avg v (fun o => F (x true) o * F (x false) o)
  let W (x : Bool→A) := avg v (F (x true))*avg v (F (x false))
  have hW :
      (avg v f)^2 = avg D W := by
    unfold f oneOexpect
    rw [avg_avg,avg_cross_sq]
  have hV :
      avg v (fun x => f x^2) = avg D V := by
    unfold f oneOexpect; simp_rw [avg_cross_sq]; rw [avg_avg]
  have hi x :
      V x-W x ≤ 2*ind (¬s.free x)+B := by
    by_cases he : s.free x
    · have hh := one_pooled_batch (s.left ∘ x) m hN k hk hK he.1
        (T ∘ x) (fun i y => hT _ _)
      simp_rw [Fintype.prod_bool] at hh
      rw [ind_zero (fun h => h he),mul_zero,zero_add]
      exact (le_abs_self _).trans hh
    have h1 (a b : ℝ) (h : |a|≤1) (g : |b|≤1) : |a*b|≤1 := by
      rw [abs_mul]
      exact (mul_le_mul h g (abs_nonneg _) zero_le_one).trans_eq (by ring)
    have hh : |W x|≤1 := h1 _ _ (avg_bound1 hv _ (fun y => hT _ _)) (avg_bound1 hv _
      (fun y => hT _ _))
    have hg : |V x|≤1 := avg_bound1 hv _ (fun i => h1 _ _ (hT _ _) (hT _ _))
    have ht : 0 ≤ twinkle (tied g Bool) k N := add_nonneg (mul_nonneg (Nat.cast_nonneg _)
      (mul_nonneg (by norm_num) (bp_pos _).le)) (bp_pos _).le
    have h2 : 0 ≤ B := mul_nonneg (mul_nonneg (by norm_num) (quadratic_net_fact_pos _).le) ht
    rw [ind_one he,mul_one]
    exact sub_le_iff_le_add.mpr (by linarith [(abs_le.mp hh).1,(abs_le.mp hg).2])
  change avg v _ ≤ _
  rw [avg_var v f hv,hW,hV,← avg_sub]
  apply (avg_mono hD.nz hi).trans
  rw [avg_add,avg_mul',hD.avg_const]
  exact add_le_add_left (mul_le_mul_of_nonneg_left hr (by norm_num)) _

end
end Lax793645Proofs.Simplifications
