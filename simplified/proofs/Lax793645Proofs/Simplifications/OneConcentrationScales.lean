import Lax793645Proofs.Simplifications.OneQueryVariance
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.ConcentrationScales

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function LinearMap Filter Real
open scoped Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I J G A : Type} [Fintype I] [Fintype J] [Fintype G] [Fintype A]
  [DecidableEq I] [DecidableEq J] [DecidableEq G] {p : Shape} {n N : ℕ}

set_option maxHeartbeats 600000 in
theorem one_variance_calendar (p : Shape) (M : ℕ) (g : Route J G)
    (r u : ℝ) (hu : 0 < u) (hM : 1≤M) :
    ∀ᶠ n : ℕ in atTop, let N := M*n; ∀ (m : Mixer p n)
      (A : Type) [Fintype A] (s : Program p n g A)
      (T : A→ Wgt (Rack J N)) (w : Wgt A), IsLaw w →
      (∀ x y, |T x y|≤1) →Fintype.card (Row p n)+2*p.h+3≤N →
      pr (draws Bool w) (fun x => ¬ s.free x) ≤ bp (r-n) →
      (let v := oneForumLaw m N
       let f := oneOexpect s w T
       avg v (fun x => (f x-avg v f)^2)) ≤ u*bp (-(1/4:ℝ)*n) := by
  let t := tied g Bool
  let k := num (Bool×J)
  let b := 2*quadraticNetFact t
  let c := num G* (2*bp k)+1
  filter_upwards [pay_div_nat (a:=1) (2*bp r) (u/2) (by positivity) (b:=1/4) (by norm_num),
    pay_div_nat (a:=1/2) (b*c) (u/2) (by positivity) (b:=1/4) (by norm_num),
    (cast_tops M hM).eventually (eventually_ge_atTop (2*k+2))]
    with n hn hh hk N m A _ s T w hw hT hN h
  change (2*k+2) ≤ (↑(M*n) : ℝ) at hk
  have he := one_oVar m hN T w hw hT k (fun i => port_limit _ i) (by linarith only [hk])
    (bp (r-n)) h
  apply he.trans
  subst N
  have hv : (n:ℝ) ≤ (M*n:ℕ) := by exact_mod_cast (show n ≤ M*n from by nlinarith)
  let P := bp (-(1/2:ℝ)*n)
  have ht : twinkle t k (M*n) ≤ c*P := by
    have hq : bp (k-(M*n:ℕ)) ≤ bp k*P := by
      unfold P; rw [← bp_add]; apply bp_le; linarith only [hv,Nat.cast_nonneg (α:=ℝ) n]
    have hr : bp (-(↑(M*n):ℝ)/2)≤P := bp_le (by linarith only [hv])
    calc _ ≤ num G*(2*(bp k * P))+P := add_le_add
                (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hq (by norm_num))
                  (Nat.cast_nonneg _)) hr
         _ = _ := by unfold c; ring
  have h1 : 2*bp (r-n) ≤ u/2*bp (-(1/4:ℝ)*n) := by
    simpa only [mul_assoc,← bp_add,neg_mul,one_mul,←sub_eq_add_neg] using hn
  have h2 : 2*quadraticNetFact t* twinkle t k (M*n)≤ u/2*bp (-(1/4:ℝ)*n) :=
    (mul_le_mul_of_nonneg_left ht (by apply mul_nonneg (by norm_num) (quadratic_net_fact_pos _).le)).trans
      (le_trans (le_of_eq (Eq.symm (mul_assoc b c P))) hh)
  exact (add_le_add h1 h2).trans_eq (by ring)

end
end Lax793645Proofs.Simplifications
