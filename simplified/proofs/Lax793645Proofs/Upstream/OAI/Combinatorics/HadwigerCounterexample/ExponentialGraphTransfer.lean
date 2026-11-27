/-
Adapted from OpenAI, openai/math, commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (Apache-2.0).
Original module: OAI.Combinatorics.HadwigerCounterexample.ExponentialGraphTransfer.
Changes: archive package namespace and imports; see references/upstream-construction.json.
-/
import Lax793645Proofs.Simplifications.MatchingNeighborhoods
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.ExponentialRates

namespace Lax793645Proofs.Upstream.OAI

/-! # Exponential Graph Transfer -/

noncomputable section
namespace HadwigerCounterexample
open HadwigerMatching Real Filter

def ord (g N : ℕ) := (2:ℕ)^(1000*g*N)
theorem cast_ord (g N : ℕ) : ((ord g N : ℕ):ℝ) = bp (1000*g*N) := by
  unfold ord
  have h := bp_nat (1000*g*N)
  push_cast at *
  exact h.symm

theorem tendsto_ord {g : ℕ} (hg : 0 < g) : Tendsto (ord g) atTop atTop := by
  have hl : Tendsto (fun n : ℕ => bp (1000*g*n)) atTop atTop :=
    (bp_tendsto (show (0:ℝ)<1000*g by positivity)).comp tendsto_natCast_atTop_atTop
  rw [tendsto_atTop]
  intro b
  filter_upwards [hl.eventually (eventually_ge_atTop (b:ℝ))] with i hi
  change _ ≤ bp _ at hi
  rw [← cast_ord] at hi
  exact_mod_cast hi

/-- Raw supersaturation ⇒ existence for the sampled order. Takes any fixed
polynomial bit-count bound of degree two for the raw unit space. In particular
the eventual N-bound is independent of every law and graph. -/
theorem transfer_scales {g : ℕ} (hg : 0 < g) {B : ℝ} (hB : 0 ≤ B) :
    ∀ᶠ N : ℕ in atTop, ∀ (A : Type) [Fintype A] [Nonempty A]
      (H : Holes A) (μ : Wgt A), IsLaw μ →
      (Fintype.card (A × A) : ℝ) ≤ bp (B * (N:ℝ)^2) →
      (∀ w : Wgt (A × A), IsLaw w → pairCaps μ (bp 1000) (bp (4000*g*N)) w →
        carried w H.unit → bp (-100*g*N) ≤ pr (pairW w w) (fun x => H.conflict x.1 x.2)) →
      ∃ x : Fin (ord g N) → A,
        (H.graph x).indepNum ≤ 2 ∧
        (connectedMatchingNumber (H.graph x) : ℚ) < (ord g N : ℚ)/100 := by
  have hg' : (1:ℝ) ≤ g := by exact_mod_cast hg
  have hh := bp_poly_dom_nat (a:=100*g) (by positivity) (B+2000000*g+10000) 2
  filter_upwards [hh, eventually_ge_atTop 1,
    (tendsto_ord hg).eventually (eventually_ge_atTop 5500)] with N hN hN' hord
  intro A _ _ H μ hμ hA hs
  let y : ℝ := g*(N:ℝ)
  have hNr : (1:ℝ) ≤ N := by exact_mod_cast hN'
  have hy : 1 ≤ y := by unfold y; nlinarith
  let m := ord g N
  let L : ℕ := 2^(200*g*N)
  let b : ℕ := 4100*g*N+6
  let k := (m+99)/100
  let s := k/5
  have hm : (m:ℝ)=bp (1000*y) := by rw [cast_ord]; unfold y; ring_nf
  have hl : (L:ℝ)=bp (200*y) := by
    have h := (bp_nat (200*g*N)).symm
    push_cast at h
    dsimp only [L]
    push_cast
    unfold y
    rwa [← mul_assoc]
  have hb : (b:ℝ)=4100*y+6 := by dsimp [b,y]; push_cast; ring
  let z : ℝ := B*(N:ℝ)^2
  have hz : 0 ≤ z := by unfold z; positivity
  have hbz : z+1 < bp (100*y) := by
    have hh : (B+2000000*g+10000)*(N:ℝ)^2 < bp (100*y) := by
      simpa only [y,mul_assoc] using hN
    unfold z
    nlinarith only [hh,hNr,hg']
  have hbudget : 384*(b:ℝ)<(L:ℝ)*bp (-100*g*N) := by
    rw [hl,← bp_add]
    have he : 200*y+ -100*(g:ℝ)*N=100*y := by dsimp [y]; ring
    rw [he,hb]
    have hh : (B+2000000*g+10000)*(N:ℝ)^2 < bp (100*y) := by
      simpa only [y,mul_assoc] using hN
    have hNN : (N:ℝ) ≤ (N:ℝ)^2 := by nlinarith
    have hgg := mul_le_mul_of_nonneg_left hNN (show 0≤(g:ℝ) by positivity)
    dsimp [y]
    nlinarith [mul_nonneg hB (sq_nonneg (N:ℝ))]
  apply Lax793645Proofs.Simplifications.MatchingNeighborhoods.matching_certificate_transfer H hμ
    (bp_pos _) (bp_pos _) (bp_pos _) hs (L:=L) (b:=b) (k:=k) (s:=s)
    (by dsimp [b]; omega) (by dsimp [k,m] at *; omega)
    (by dsimp [k]; omega) (by dsimp [s]; omega) ?_ hbudget ?_
  · have h32 : bp 5=32 := by have h := bp_nat 5; norm_num at h; exact h
    rw [← bp_nat,← h32,← bp_sub,← bp_add,hb]
    apply bp_le
    dsimp [y]
    linarith
  · have hms : (m:ℝ) ≤ 550*s := by
      have hn : m ≤ 550*s := by dsimp [s,k]; omega
      exact_mod_cast hn
    have hm' : (5500:ℝ) ≤ m := by exact_mod_cast hord
    let a := (Fintype.card (A × A):ℝ)+1
    have ha : a ≤ bp (z+1) := by
      rw [bp_add,bp_one]
      have hx : 1 ≤ bp z := by simpa only [bp_zero] using bp_le hz
      change _ ≤ bp z at hA
      dsimp only [a]
      linarith only [hx,hA]
    have hal : a^L ≤ bp ((m:ℝ)/2) := calc
      a^L ≤ bp (z+1)^L := by
        have hp : 0 ≤ a := by dsimp [a]; positivity
        gcongr
      _ = bp ((z+1)*L) := (bp_mul_nat _ _).symm
      _ ≤ bp ((m:ℝ)/2) := bp_le (by
        rw [hm,hl]
        calc (z+1)*bp (200*y) ≤ bp (100*y)*bp (200*y) :=
               mul_le_mul_of_nonneg_right hbz.le (bp_pos _).le
             _ = bp (300*y) := by rw [← bp_add]; congr 1; ring
             _ ≤ bp (1000*y)/2 := by
               rw [← bp_one,← bp_sub]
               exact bp_le (by linarith only [hy]))
    let d := bp (4000*(g:ℝ)*(N:ℝ))
    have he₁ : 8/bp 1000=bp (3-1000) := by
      have h8 : bp 3=8 := by have h := bp_nat 3; norm_num at h; exact h
      rw [bp_sub,h8]
    have he₂ : 4/d=bp (2-4000*y) := by
      rw [bp_sub]
      have ht : bp 2=(4:ℝ) := by have h := bp_nat 2; norm_num at h; exact h
      rw [ht]
      congr 2
      dsimp [d,y]
      congr 1
      ring
    have ha1 : bp ((m:ℝ)/2)*((2:ℝ)^m*(8/bp 1000)^s) ≤ bp (-(m:ℝ)/4) := by
      rw [← bp_nat,he₁,← bp_mul_nat,← bp_add,← bp_add]
      apply bp_le
      linarith
    have ha2 : bp ((m:ℝ)/2)*((m:ℝ)^(s+s)*(4/d)^s) ≤ bp (-(m:ℝ)/4) := by
      have he : (m:ℝ)^(s+s)=bp ((1000*y)*(s+s:ℕ)) := by rw [hm,bp_mul_nat]
      rw [he,he₂,← bp_mul_nat,← bp_add,← bp_add]
      apply bp_le
      push_cast
      have hx : (s:ℝ) ≤ y*s := by nlinarith [show (0:ℝ) ≤ (s:ℝ) from Nat.cast_nonneg s]
      nlinarith
    have hx : bp (-(m:ℝ)/4)<1/16 := by
      have h16 : bp 4=16 := by have h := bp_nat 4; norm_num at h; exact h
      rw [show (1:ℝ)/16=bp (-4) by rw [bp_neg,h16]; norm_num]
      exact bp_lt (by linarith only [hm'])
    change a^L*((2:ℝ)^m*(8/bp 1000)^s+(m:ℝ)^(s+s)*(4/d)^s)<1/8
    refine lt_of_le_of_lt (mul_le_mul_of_nonneg_right hal (by
      have hd : 0<d := bp_pos _
      have hM0 := bp_pos 1000
      positivity)) ?_
    linarith only [ha1,ha2,hx]

end HadwigerCounterexample

end

end Lax793645Proofs.Upstream.OAI
