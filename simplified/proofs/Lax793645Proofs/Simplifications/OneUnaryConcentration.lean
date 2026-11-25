import Lax793645Proofs.Simplifications.OneUnaryReference
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.UnaryQueryFrequencies

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function LinearMap Filter Real
open scoped Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N : ℕ}

def oneMinorCall (v : Template.Solo p) (w : Wgt (Knobs p.g n))
    (T : Wgt (OneAtomKey (p:=p) (v.t ()) N)) (o : OneOrient p n N) :=
  avg w (fun i => T (oneDesc v i o))

set_option maxHeartbeats 600000 in
theorem one_flat_recital (v : Template.Solo p) (M : ℕ) (hM : 1 ≤ M) (hj : 1≤p.j) (ε : ℝ)
    (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop, let N := M*n; ∀ (m : Mixer p n)
      (w : Wgt (Knobs p.g n)) (q : F), IsLaw w →
      carried w (fun x => dialed p (v.t ()) (v.f ()) x=q) →
      mapW w (freePart p)=unif → Fintype.card (Row p n)+2*p.h+3≤N →
      ∀ T : Wgt (OneAtomKey (p:=p) (v.t ()) N), (∀ x,|T x|≤1) →
      pr (oneRaw m N) (fun x => ε≤|oneMinorCall v w T x - avg (oneLawOmega p N (v.t ()) q) T|) ≤
        bp (-(1/8:ℝ)*n) := by
  classical
  let c := ε/2; have hc : 0<c := by positivity
  let g := ownPort (p:=p) v.t
  let k := num (KeySlots p v.t)
  let D := 2 * quadraticNetFact g * (num (Comp p.g)* (2*bp k))
  filter_upwards [one_raw_variance v M hM,
    pay_div_nat (a:=1) D c hc (b:=0) zero_lt_one,
    pay_div_nat (a:=1/4) 1 (c^2) (by positivity) (b:=1/8) (by norm_num),
    (cast_tops M hM).eventually (eventually_ge_atTop (2*k+2))]
    with n hn hY hD hl N m w q hw he hZ hN T hT
  let μ := oneRaw m N
  have hμ : IsLaw μ := one_raw_law m (by omega)
  let u := oneMinorCall v w T
  let b := avg (oneLawOmega p N (v.t ()) q) T
  have hR : 2 * quadraticNetFact g * (num (Comp p.g)*(2*bp (k-N))) ≤ c := by
    have hz : 0 ≤ D := by
      unfold D; apply mul_nonneg (mul_nonneg (by norm_num) (quadratic_net_fact_pos _).le)
      exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (by norm_num) (bp_pos _).le)
    have hq : (n:ℝ) ≤ N := by
      exact_mod_cast (show n ≤ N from (by unfold N; nlinarith))
    have hH : bp (-(N:ℝ))≤ bp (-(n:ℝ)) := bp_le (by linarith only [hq])
    refine le_trans ?_ ((mul_le_mul_of_nonneg_left hH hz).trans (by simpa using hY))
    rw [sub_eq_add_neg,bp_add]; unfold D; ring_nf; exact le_rfl
  change 2*k+2 ≤ (N:ℝ) at hl
  have hi : |avg μ u-b| ≤ c := by
    unfold u oneMinorCall
    rw [avg_avg,← hw.avg_const b,← avg_sub]
    refine (abs_avg_le hw.nz).trans ?_
    rw [←hw.avg_const c]
    unfold avg
    apply Finset.sum_le_sum; intro i _
    by_cases h : w i=0
    · rw [h]; simp
    have hy :
        |avg μ (T ∘ oneDesc v i)-b|≤ c := le_trans
      (one_solo_read v m hN i q hj (not_not.mp fun he' => h (he i he'))
        T hT k (port_limit g) (by linarith only [hl])) hR
    exact mul_le_mul_of_nonneg_left hy (hw.nz i)
  have heV :
      avg μ (fun x => (u x-avg μ u)^2)≤ bp (-(1/4:ℝ)*n) := by
    let F (i : Inputs p n Unit) (y : OneKeys (p:=p) v.t N) := T (y ())
    have ht := hn m (fun i=>w) (fun i=>hw) (fun i=>hZ) hN F (fun i j=>hT _)
    have he' : u=fun o : OneOrient p n N =>
        avg (prodW (fun _ : Unit => w)) (fun z =>
          F z (fun i => oneCallOne v i (z i) o)) := by
      funext i
      let f (x : Knobs p.g n) := T (oneDesc v x i)
      have hz : avg (mapW (draws Unit w) (fun x => x ())) f = _ :=
        mapW_avg (draws Unit w) _ f
      rw [draw_pick hw] at hz
      exact hz
    rw [he']; exact ht
  change pr μ (fun x => ε≤ |u x-b|)≤_
  have heQ x (h : ε≤|u x-b|) : c≤ |u x-avg μ u| := by
    have hh := abs_sub_le (u x) (avg μ u) b
    unfold c at *; linarith only [h,hh,hi]
  refine (pr_mono hμ.nz heQ).trans ((outlier hμ.nz _ _ hc heV).trans ?_)
  rw [div_le_iff₀ (by positivity : 0<c^2)]
  simpa [mul_comm] using hD
end
end Lax793645Proofs.Simplifications
