import Lax793645Proofs.Simplifications.ExactBaseQueryComparison
import Lax793645Proofs.Simplifications.BaseQueryHits

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis StatusAnalysis.Quill Template Filter Finset Matrix Function
open scoped BigOperators Topology Classical
noncomputable section
variable {p : Shape} {M n N K r s0 : ℕ} {b' : PreparationParameters}
  {q : Format} {d : Rates} {b : Bool}
  (w : Quill p q d b) (t : Tagging p (Messenger q)) (z : Messenger q→F)

set_option maxHeartbeats 1400000 in
/-- Exponential exceptional mass for a large exact product test. This
version uses binary mixing and unary concentration directly. -/
theorem exact_base_sober_gain (h:QueryParameters p M b' s0) (hw : w.moral t z) (paints : ℕ) (ε:ℝ) (he:0<ε) :
    ∃ c:ℝ,0<c ∧ ∀ᶠ n:ℕ in atTop,let N:=M*n;let K:=b'.pins;
      ∀ (m:Mixer p n) (U:Wgt (UnitType p n N)), b'.Align s0 p M n m U →
      ∀ H : Keys (p:=p) t N→Prop, design (w.pen t) (fun x=>ind (H x)) 1 paints → ε≤pr (lawNu p N t z) H →
      pr U (fun i=>¬w.baseSober t z K H m (w.dilate t K*(ε/4)) i) ≤ bp (-c*n) := by
  classical
  let K:=b'.pins
  let α:=w.dilate t K*(ε/4)
  have hα :0<α:=mul_pos (dilate_pos ..) (by positivity)
  obtain ⟨r,u,c,hu,hc,hR⟩:= exact_base_paint_side_release w t z M h hw paints α hα
  let I:=Messenger q; let D:=num I; have hD : 0 ≤ D:=Nat.cast_nonneg _
  let β:= ε/(4*(D+1)*(r+1:ℝ)); let δ:=min u β
  have hd : 0<δ:= lt_min hu (show 0<β from by unfold β; positivity)
  have hδ : D*(r:ℝ)*δ ≤ ε/4 := by
    have hi : δ* (4*(D+1)*(r+1:ℝ)) ≤ ε := (le_div_iff₀ (by positivity)).mp (min_le_right ..)
    have hh :  D*(r:ℝ) ≤ (D+1)*(r+1:ℝ) := mul_le_mul (by linarith) (by linarith)
      (by positivity) (by positivity)
    linarith only [hi,mul_le_mul_of_nonneg_right hh hd.le]
  have hq:=h.enter.first
  let k:ℝ:=min c (1/100)
  have hk:0<k:=lt_min hc (by norm_num)
  refine ⟨k/2,half_pos hk,?_⟩
  let L:=2*netFact (trayPort p t)
  have hz:= (trend_sizes atTop (le_refl _) hq.hM).2
  have hX : ∀ᶠ n : ℕ in atTop,D*(L*bp (-((M*n:ℕ):ℝ)/2))≤ε/4 := by
    have heq:=((((bp_tendsto_zero (by norm_num: 0<(1/2:ℝ))).comp hz).const_mul L).const_mul D)
    have hx : ∀ᶠ n : ℕ in atTop,D*(L*bp (-(1/2:ℝ)*((M*n:ℕ):ℝ)))≤ ε/4 := heq.eventually
      (eventually_le_nhds (by rw [mul_zero,mul_zero]; positivity))
    filter_upwards [hx] with n hn; rw [show -((M*n:ℕ):ℝ)/2= -(1/2:ℝ)*((M*n:ℕ):ℝ) from by ring]
    exact hn
  filter_upwards [hR,hX,gauzeCalendar p r M h δ δ hd hd,pay_nat (a:=k) 2 (half_lt_self hk),
    hz.eventually (eventually_ge_atTop (2*num (Toast p)+1)),
    hz.eventually (eventually_ge_atTop (2*num (I×Toast p)+1))]
    with n hn hx hv he' hG hI N K m U hm H hdesign hH
  let W:=fun x=> ind (H x)
  obtain ⟨Y,hY⟩:=hn W hdesign
  let F:= w.baseFlunk t z Y W m u α
  let Q i:= ¬gauze p δ δ Y m K i
  have h1 :pr U F≤bp (-c*n) := hY r Y (self_refine Y) _ _ hm
  have h2 :pr U Q ≤bp (-(1/100:ℝ)*n) := hv _ _ hm Y
  have hhN : 2*num (Messenger q×Toast p)-(N:ℝ)≤ -1 := by
    change 2*num (Messenger q×Toast p)+1 ≤ (N:ℝ) at hI; linarith only [hI]
  have ht : 2*num (Toast p)-(N:ℝ) ≤ -1 := by
    change _≤(N:ℝ) at hG; linarith only [hG]
  have h3 o (h :¬w.baseSober t z K H m α o) : F o ∨ Q o := by
    by_contra! hh
    obtain ⟨s,hg,hl⟩:= show ∃ s,w.baseSteady m K s o∧ w.baseProwl t z s m o W<α from by
      unfold baseSober at h; push Not at h; exact h
    have hσ : gauze p δ δ Y m K o := not_not.mp hh.2
    have ht := w.baseSheen_hit t z m Y o s H hd hH hw hq.hR hm.age hg hhN ht
      (show D*(r*δ+L*bp (-(N:ℝ)/2))≤ε/2 by
        change _*(L*bp (-(N:ℝ)/2)) ≤_ at hx; linarith only [hx,hδ]) hσ
    refine hh.1 ⟨hg.frame,Station.gauzed_area _ _ _ _ hw δ (min_le_left ..)
      _ hσ,s,?_⟩
    rw [abs_sub_comm]
    refine lt_of_lt_of_le ?_ (le_abs_self _); unfold α W at *
    linarith only [ht,hl]
  have ht (x:ℝ) (hx : k≤x): bp (-x*n) ≤ bp (-k*n) := bp_le
    (mul_le_mul_of_nonneg_right (neg_le_neg hx) (Nat.cast_nonneg _))
  rw [two_mul] at he'
  have hg:=hm.drain.1
  exact ((pr_mono hg.nz h3).trans (pr_or_le hg.nz)).trans
    ((add_le_add (h1.trans (ht _ (min_le_left ..))) (h2.trans (ht _ (min_le_right ..)))).trans he')


theorem exact_base_sober_calendar (h:QueryParameters p M b' s0)
    (hw : w.moral t z) (paints : ℕ) (ε:ℝ) (he:0<ε) :
    ∃ (α c:ℝ),0<α∧0<c ∧ ∀ᶠ n:ℕ in atTop,let N:=M*n;let K:=b'.pins;
      ∀ (m:Mixer p n) (U:Wgt (UnitType p n N)), b'.Align s0 p M n m U →
      ∀ H : Keys (p:=p) t N→Prop, design (w.pen t) (fun x=>ind (H x)) 1 paints → ε≤pr (lawNu p N t z) H →
      pr U (fun i=>¬w.baseSober t z K H m α i) ≤ bp (-c*n) := by
  obtain ⟨c,hc,hcal⟩:=exact_base_sober_gain w t z h hw paints ε he
  exact ⟨w.dilate t b'.pins*(ε/4),c,mul_pos (w.dilate_pos t b'.pins) (by positivity),hc,hcal⟩

end
end Lax793645Proofs.Simplifications
