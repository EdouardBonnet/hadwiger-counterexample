import Lax793645Proofs.Simplifications.OneOffsetFourierBounds

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Module Submodule Function Finset
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {p : Shape} {n N r : ℕ} {T : SymCover p (2*N)}

def oneGlimpseBill (p : Shape) (r : ℕ) (H : ℝ):=num (Comp p.g)*(H*2*bp ((r:ℝ)-p.h))

theorem one_tuple_glimpse_failure {q : Comp p.g→ℕ}
    (A : ImageTuple (Comp p.g) q (2*N)) (hA : ∀ e,Injective (A e).mulVec)
    (hq : ∀ e,q e≤r) {w : Wgt (OneUnit p n N)} (hw : SubLaw w)
    (m : Mixer p n) (i : Bool) {H : ℝ} (hH : 0≤H)
    (hside : ∀ o,mapW w (fun x=>x i) o≤H*oneRaw m N o)
    (hroom : Fintype.card (Row p n)+2*p.h+1≤N) :
    pr w (fun x=>¬oneTupleGlimpse x i A)≤oneGlimpseBill p r H := by
  classical
  let E (e : Comp p.g) (x : OneUnit p n N):=¬Injective ((onePhaseCube (x i) e).1ᵀ*A e).mulVec
  have he x : ¬oneTupleGlimpse x i A↔∃ e,E e x:=by exact not_forall
  simp_rw [he]
  apply (pr_exists_le hw.nz E).trans
  have hb e : pr w (E e)≤H*2*bp ((r:ℝ)-p.h):=
    (one_unit_glimpse_failure m hH i hside hroom e (A e) (hA e)).trans
      (mul_le_mul_of_nonneg_left (bp_le (sub_le_sub_right (by exact_mod_cast hq e) _)) (by positivity))
  exact (Finset.sum_le_sum (fun e _=>hb e)).trans_eq (by simp [oneGlimpseBill,num])

namespace OneBazaar
variable (s : OneBazaar p n r T)

/-- The singleton phase estimate for the actual quadratic frame law.
The diagonal correction is retained as a bounded separate Walsh weight. -/
theorem single_pitch {w : Wgt (OneUnit p n N)} {Δ : OneUnit p n N→Ambient p (2*N)}
    (hopen : s.opened Δ w) (hw : IsLaw w) (i : Bool) (R : Party)
    (m : Mixer p n) {H ζ : ℝ} (hH : 0≤H)
    (hside : ∀ i o,mapW w (fun x=>x i) o≤H*oneRaw m N o)
    (hroom : Fintype.card (Row p n)+2*p.h+1≤N)
    (hcap : ∀ a : ImagePin (Comp p.g) (OneColumn p n) (2*N),
      pr (oneUnitRaw m N) (imagePinAgree oneDualImages a)≤fee (2*N) ζ (imagePlanRank a.sp))
    (hp : oneSelectionPrice p r n N H ζ)
    (ht : num (SymAtlas p r T)≤bp (0.002*(2*N))) :
    |channelPitch Δ oneListens w (unary i) R|≤oneGlimpseBill p r H+bp (-0.24*(2*N)) ∧
    ((∀ x,w x≠0→∀ y,w y≠0 → oneTupleGlimpse y i (symSrc (s.ix x)))→
      |channelPitch Δ oneListens w (unary i) R|≤bp (-0.24*(2*N))) := by
  classical
  let C : OneSales p n r T:=fun M _ y=>oneTupleGlimpse y i (symSrc M)
  have hA M:=bag_rate m hH hw.sub hside hroom hcap hopen hp M i
  have hB M G hM hG:=glimpse_prize m hH hw.sub hside hroom hcap hopen hp M G i hM hG
    (C M G) (fun _ _ h=>h)
  have hf:=s.beat_mix hopen hw (unary i) R i C hA hB ht
  have he : discard (s:=s) w C=avg w (fun x=>pr w (fun y=>¬oneTupleGlimpse y i (symSrc (s.ix x)))):=
    pairW_avg ..
  rw [he] at hf
  constructor
  · apply hf.trans (add_le_add_left ?_ _)
    rw [←hw.avg_const (oneGlimpseBill p r H)]
    apply avg_on_support hw.nz
    intro x hx
    have hs:=(hopen x hx).1
    exact one_tuple_glimpse_failure (symSrc (s.ix x)) hs.2.2.1
      (fun e=>((Finset.single_le_sum (fun e _=>Nat.zero_le (symBreadth (s.ix x) e))
        (Finset.mem_univ e)).trans hs.2.1)) hw.sub m i hH (hside i) hroom
  intro hh
  have hz : avg w (fun x=>pr w (fun y=>¬oneTupleGlimpse y i (symSrc (s.ix x))))=0 := by
    rw [←hw.avg_const 0]
    apply avg_congr
    intro x hx
    rw [←hw.avg_const 0]
    exact avg_congr (fun y hy=>ind_zero (by simp [hh x hx y hy]))
  rwa [hz,zero_add] at hf

end OneBazaar
end
end Lax793645Proofs.Simplifications
