/-
Adapted finite scale/refinement calculations from OpenAI, openai/math,
commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (Apache-2.0).
The new proofs use repeated hits and quadratic energy instead of entropy.
-/
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.HistogramEnergyScales

/-! Many-query Fourier scales for cells as small as an exponential in n.
Only the frame, peak and density estimates are needed; there is no entropy charge. -/
namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Real Filter
open scoped BigOperators Topology
noncomputable section

structure OneHitBar (M : ℕ) (C : ℝ) (I J G : Type) [Fintype I] [Fintype J]
    [Fintype G] [DecidableEq G] (g : Route J G) (n l : ℕ) (u E : ℝ) : Prop where
  pos : 0<l
  frame : ∀ i : G, 2*num (Port (tied g (Fin l)) i)+2 ≤ ↑(M*n)
  peak : peakExpense (Fin l) J 1+ (-(↑(M*n):ℝ)/2+2*u) ≤0
  cap : bp (C*(M*n:ℕ))*((4:ℝ)^Fintype.card G * bp (num (Fin l)*num J*num J) *
    (num (Fin l × J)+1)) ≤ bp (E*l)

set_option maxHeartbeats 800000 in
theorem one_hit_scales (M : ℕ) (hM : 1≤M) (C : ℝ) (hC : 0≤C)
    (I J G : Type) [Fintype I] [Fintype J]
    [Fintype G] [DecidableEq G] (g : Route J G) :
    ∃ (s : ℕ) (α E : ℝ), 0<s ∧ 0<α ∧ α≤1/4 ∧ 0≤E ∧
      ∀ᶠ n : ℕ in atTop,
        (n:ℝ)≤2*s*(n/s:ℕ) ∧
        num (Fin (n/s))*num I-n ≤ -(1/2:ℝ)*n ∧
        OneHitBar M C I J G g n (n/s) (α*n) E := by
  classical
  let a := num I; let b := num J
  let d := 2*((1+2*b)*b)
  have ha : 0≤a := Nat.cast_nonneg _
  have hb : 0≤b := Nat.cast_nonneg _
  have hd : 0 ≤ d := by positivity
  obtain ⟨s,hs⟩ := exists_nat_gt (2+4*(a+b+d))
  have hs' : 0<s := by exact_mod_cast (show (0:ℝ)<s from by linarith)
  have hi : (1:ℝ)≤M := by exact_mod_cast hM
  let E := C*(M*2*s)+b*b+1
  have hM' : (0:ℝ)≤M := by positivity
  have hE : 0 ≤ E := by positivity
  let α : ℝ := 1/(16*s)
  have hα : 0<α := by positivity
  have hs1 : (1:ℝ)≤s := by exact_mod_cast hs'
  have hα' : α≤1/4 := by unfold α; rw [div_le_iff₀ (by positivity)]; linarith
  refine ⟨s,α,E,hs',hα,hα',hE,?_⟩
  have ht := div_grows s hs'
  let B := (4:ℝ)^Fintype.card G
  filter_upwards [ht.eventually (eventually_ge_atTop 1),
    ht.eventually (bp_poly_dom_nat (a:=1) (by norm_num) (B*(b+1)) 1)]
    with n hl hG
  let u := α*n
  let l := n/s
  have hl' : 1≤(l:ℝ) := by exact_mod_cast hl
  have hsl : (s:ℝ)*l ≤ n := by
    rw [mul_comm]; exact_mod_cast Nat.div_mul_le_self n s
  have hnl : (n:ℝ) ≤ 2*s*l := by
    have h := Nat.lt_mul_div_succ n hs'
    change n<s*(l+1) at h
    have h1 : (n:ℝ)≤s*((l:ℝ)+1) := by exact_mod_cast h.le
    nlinarith only [h1,mul_le_mul_of_nonneg_left hl' (Nat.cast_nonneg (α:=ℝ) s)]
  have hx : (n:ℝ) ≤ ↑(M*n) := by
    exact_mod_cast (show n ≤ M*n from by nlinarith)
  have hpeak : 8*u≤(l:ℝ) := by
    have he : 8*u = (n:ℝ)/(2*s) := by unfold u α; field_simp; ring
    rw [he, div_le_iff₀ (by positivity)]
    nlinarith only [hnl]
  have hh1 := mul_le_mul_of_nonneg_right hs.le (Nat.cast_nonneg l : 0≤(l:ℝ))
  have hq :
      num (Fin l)=(l:ℝ) ∧ num (Fin l × J)=(l:ℝ)*b := by simp [num,b]
  refine ⟨hnl,?_,?_⟩
  · change num (Fin l)*a-n ≤ -(1/2:ℝ)*n
    rw [hq.1]
    nlinarith only [hh1,hsl,
      mul_nonneg hb (Nat.cast_nonneg l : 0≤(l:ℝ)),
      mul_nonneg hd (Nat.cast_nonneg l : 0≤(l:ℝ)),Nat.cast_nonneg (α:=ℝ) l]
  constructor
  · exact hl
  · intro i
    change 2*num (Port (tied g (Fin l)) i)+2 ≤ ↑(M*n)
    have hg := port_limit (tied g (Fin l)) i
    rw [hq.2] at hg
    nlinarith only [hg,hx,hsl,hl',hh1,
      mul_nonneg ha (Nat.cast_nonneg l : 0≤(l:ℝ)),
      mul_nonneg hb (Nat.cast_nonneg l : 0≤(l:ℝ)),
      mul_nonneg hd (Nat.cast_nonneg l : 0≤(l:ℝ))]
  · have he : peakExpense (Fin l) J 1=d*l := by unfold peakExpense d b; rw [hq.1]; norm_num; ring
    change peakExpense (Fin l) J 1+ _ ≤ _
    rw [he]
    nlinarith only [hh1,hsl,hx, hpeak,
      mul_nonneg ha (Nat.cast_nonneg l : 0≤(l:ℝ)),
      mul_nonneg hb (Nat.cast_nonneg l : 0≤(l:ℝ)),
      mul_nonneg hd (Nat.cast_nonneg l : 0≤(l:ℝ)), Nat.cast_nonneg (α:=ℝ) l]
  · change bp _ * (B *bp (num (Fin l)*b*b) * (num (Fin l×J)+1)) ≤ bp (E*l)
    have hg : B*(num (Fin l×J)+1) ≤ bp l := by
      change B*(b+1)*(l:ℝ)^1 < bp (1*l) at hG
      simp only [hq.2]; rw [pow_one,one_mul] at hG
      refine le_trans ?_ hG.le
      exact (mul_le_mul_of_nonneg_left (show (l:ℝ)*b+1≤(b+1)*l by linarith only [hl'])
        (by positivity)).trans_eq (Eq.symm (mul_assoc _ _ _))
    have he : C*(↑(M*n):ℝ) ≤ C*(M*2*s)*l := by
      rw [Nat.cast_mul]
      exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hnl hM') hC).trans_eq (by ring)
    rw [show E*l=C*(M*2*s)*l+num (Fin l)*b*b+l by rw [hq.1]; unfold E; ring,bp_add,bp_add]
    let D := num (Fin l)*b*b
    calc bp _*_ = (bp (C*↑(M*n))*bp D)*(B*(num (Fin l×J)+1)) := by unfold D; ring
         _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_right (bp_le he) (bp_pos D).le) hg
           (by unfold B num; positivity) (mul_nonneg (bp_pos _).le (bp_pos D).le)

end
end Lax793645Proofs.Simplifications
