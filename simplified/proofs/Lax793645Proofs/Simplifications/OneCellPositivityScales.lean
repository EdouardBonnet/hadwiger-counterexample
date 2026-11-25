import Lax793645Proofs.Simplifications.OneSurrogateStatusLaws
import Lax793645Proofs.Simplifications.OneUnaryPositivity
import Lax793645Proofs.Simplifications.OneInjectionTransfer

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis Filter Finset Matrix Function Template
open scoped BigOperators Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N K M r : ℕ}

structure OneUnaryParameters (p : Shape) (M K s : ℕ) : Prop where
  hM : 1≤M
  hg : Odd p.g
  hJ : 1≤p.j
  hR : 1≤p.r
  profiles : 2*profileA p K<s
  gleaming : bp (-((p.J-s:ℕ):ℝ))*bp s<glintRate K

namespace OneAppearance
variable (x : Appearance p) {s0 : ℕ}

theorem oneReadCap (x : Appearance p) (r M : ℕ) (h : OneUnaryParameters p M K s0)
    (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop, let N:=M*n; ∀ m : Mixer p n,Fintype.card (Row p n)+2*p.h+3≤N →
    ∀ Y : OneSilhouette p N r,pr (oneRaw m N) (fun o=> x.apt∧¬ oneClose x Y o ε)≤bp (-(1/16:ℝ)*n) := by
  classical
  have hp:=h
  by_cases ha : x.apt
  · let δ : ℝ := ε/(r+1:ℝ)
    have hδ : 0<δ:=by unfold δ; positivity
    filter_upwards [one_flat_recital x.trot M hp.hM hp.hJ δ hδ,eventually_ge_atTop (2*p.r),
      pay_nat (a:=1/8) (b:=1/16) (num (Fin r)) (by norm_num)] with n hn ht hB N m hN Y
    let w:= x.wit n; let v:= oneRaw m N
    have hw : IsLaw w:= Appearance.witLaw ha hp.hR ht
    let P (i : Fin r) (o : OneOrient p n N):=
      δ≤ |oneEmpirical x Y o i - oneReference x Y i|
    have hk (i : Fin r) : pr v (P i) ≤ bp (-(1/8:ℝ)*n) := by
      let S (z) := ind (Y x.l x.q z=i)
      have hf z : |S z|≤1 := by unfold S; rw [abs_of_nonneg (ind_nonneg _)]; exact ind_le_one _
      refine hn m w x.q hw (normW_carried (subW_carried _ _))
        (scopedZ_bit p n _ _ _ hw) hN S hf
    have he (o : OneOrient p n N) (h : x.apt∧¬oneClose x Y o ε) : ∃ i,P i o := by
      by_contra! hh
      apply h.2
      unfold oneClose varOne
      calc _ ≤ ∑ i : Fin r,δ:= Finset.sum_le_sum fun i _=>le_trans (abs_sub_comm ..).le
             (le_of_not_ge (hh i))
           _ ≤ ε := by
             simp; unfold δ
             calc _ ≤ ((r:ℝ)+1)* (ε/(r+1:ℝ)) := mul_le_mul_of_nonneg_right (by linarith) hδ.le
                  _ = ε := by field_simp
    have hv : IsLaw v:= one_raw_law (N:=N) m (by omega)
    exact ((pr_mono hv.nz he).trans (pr_exists_le hv.nz P)).trans
      (((Finset.sum_le_sum fun i _=>hk i).trans_eq (by simp [num])).trans hB)
  filter_upwards with n N m hN Y
  simp_rw [show (x.apt)=False from eq_false ha,false_and,pr_false]; exact (bp_pos _).le

def oneFoil (x : Appearance p) (Y : OneSilhouette p N r) (o : OneOrient p n N)
    (m : Mixer p n) (K : ℕ) (δ : ℝ) :=
    ∀ (z:Digest p.g) (i:Fin r), z.feasible x.l x.f → z.sumBit=x.q →
      δ ≤ oneReference x Y i → onePatrol x.trot m (scopedScan p n x.l x.f z)
        (fun y => Y x.l x.q y=i) K x.q o

theorem oneFoilCap (x : Appearance p) (r M : ℕ) (h : OneUnaryParameters p M K s0)
    (δ:ℝ) (hδ:0<δ) :
    ∀ᶠ n : ℕ in atTop, let N:=M*n; ∀ m : Mixer p n,Fintype.card (Row p n)+2*p.h+3≤N →
      unaryGood m K s0 → ∀ Y: OneSilhouette p N r,
      pr (oneRaw m N) (fun i=>¬oneFoil x Y i m K δ)≤bp (-(1/18:ℝ)*n) := by
  classical
  have ht:=h
  let A:= Digest p.g × Fin r
  let Q n (m:Mixer p n) (Y:OneSilhouette p (M*n) r) (a : A) (o : OneOrient p n (M*n)) :=
    a.1.feasible x.l x.f ∧ a.1.sumBit=x.q ∧ δ≤oneReference x Y a.2 ∧
      ¬onePatrol x.trot m (scopedScan p n x.l x.f a.1)
        (fun y=>Y x.l x.q y=a.2) K x.q o
  have hg (a:A) :
      ∀ᶠ n:ℕ in atTop,let N:=M*n;∀ m:Mixer p n,Fintype.card (Row p n)+2*p.h+3≤N →
        unaryGood m K s0→∀ Y:OneSilhouette p N r,
          pr (oneRaw m N) (Q n m Y a) ≤ bp (-(1/16:ℝ)*n) := by
    by_cases hf : a.1.feasible x.l x.f ∧ a.1.sumBit=x.q
    · filter_upwards [one_patrolled x.trot M ht.hM ht.hg ht.hJ a.1 hf.1 ht.hR δ hδ h.profiles
        h.gleaming] with n hn N m hN hM Y
      by_cases he : δ ≤ oneReference x Y a.2
      · let S : OneAtomKey (p:=p) (x.trot.t ()) (M*n) →Prop := fun i=>Y x.l x.q i=a.2
        let v:=scopedScan p n (x.trot.t ()) (x.trot.f ()) a.1
        have hx : δ ≤ pr (oneLawOmega p (M*n) (x.trot.t ()) a.1.sumBit) S := by
          rw [hf.2]; exact he
        have hh (i:OneOrient p n (M*n)) (h:Q n m Y a i) :
            ¬onePatrol x.trot m v S K a.1.sumBit i := hf.2 ▸ h.2.2.2
        exact (pr_mono (one_raw_law (N:=N) m (by omega)).nz hh).trans (hn m hM hN S hx)
      have hg : Q n m Y a=fun _=> False :=
        funext fun i=> eq_false (fun h=>he h.2.2.1)
      change pr (oneRaw m (M*n)) (Q n m Y a) ≤ _
      rw [hg,pr_false]; exact (bp_pos _).le
    filter_upwards with n N m hN hg Y
    have hh : Q n m Y a=fun _=> False :=
      funext fun i=> eq_false (fun h=> hf ⟨h.1,h.2.1⟩)
    change pr (oneRaw m (M*n)) (Q n m Y a) ≤ _
    rw [hh,pr_false]; exact (bp_pos _).le
  filter_upwards [eventually_all.mpr hg,pay_nat (a:=1/16) (b:=1/18) (num A) (by norm_num)]
    with n hn hB N m hN hM Y
  have he o (h : ¬oneFoil x Y o m K δ) : ∃ i, Q n m Y i o := by
    unfold oneFoil at h
    push Not at h
    obtain ⟨z,i,h⟩:=h
    exact ⟨(z,i),h⟩
  let v:=oneRaw m N
  have hv : IsLaw v:=one_raw_law (N:=N) m (by omega)
  exact ((pr_mono hv.nz he).trans (pr_exists_le hv.nz _)).trans
    (((Finset.sum_le_sum fun i _=>hn i m hN hM Y).trans_eq (by simp [num])).trans hB)
end OneAppearance

open OneAppearance

def oneSmoothSilk (p : Shape) (ε δ:ℝ) (Y:OneSilhouette p N r)
    (m:Mixer p n) (K:ℕ) (o:OneOrient p n N) :=
    ∀ x : Appearance p,(x.apt → oneClose x Y o ε) ∧ oneFoil x Y o m K δ

variable {s0 : ℕ}

def oneGauze (p : Shape) (ε δ:ℝ) (Y:OneSilhouette p N r)
    (m:Mixer p n) (K:ℕ) (o:OneUnit p n N) :=
  ∀ i,oneSmoothSilk p ε δ Y m K (o i)

private theorem one_silken (p : Shape) (r M : ℕ) (h : OneUnaryParameters p M K s0)
    (ε δ : ℝ) (he:0<ε) (hd:0<δ) :
    ∀ᶠ n : ℕ in atTop, let N:=M*n; ∀ m : Mixer p n,Fintype.card (Row p n)+2*p.h+3≤N →
      unaryGood m K s0 → ∀ Y: OneSilhouette p N r,
      pr (oneRaw m N) (fun i=>¬oneSmoothSilk p ε δ Y m K i)≤bp (-(1/20:ℝ)*n) := by
  classical
  let A:= Appearance p
  filter_upwards [eventually_all.mpr (fun x:A=>OneAppearance.oneFoilCap x r M h δ hd),
    eventually_all.mpr (fun x:A=>OneAppearance.oneReadCap x r M h ε he),
    pay_nat (a:=1/18) (b:=1/20) (num A*2) (by norm_num)] with n hn ht hB N m hN hM Y
  let v:=oneRaw m N
  have hv : IsLaw v:=one_raw_law (N:=N) m (by omega)
  let P (x:A) (o:OneOrient p n N) :=
    (x.apt ∧ ¬oneClose x Y o ε)∨ ¬oneFoil x Y o m K δ
  have hk x : pr v (P x) ≤ 2*bp (-(1/18:ℝ)*n) := by
    rw [two_mul]; apply (pr_or_le hv.nz).trans
    refine add_le_add ((ht x m hN Y).trans (bp_le ?_)) (hn x m hN hM Y)
    linarith [(Nat.cast_nonneg n :0≤(n:ℝ))]
  have hi o (h : ¬oneSmoothSilk p ε δ Y m K o) : ∃ i, P i o := by
    unfold oneSmoothSilk at h
    obtain ⟨i,h⟩:= Classical.not_forall.mp h
    exact ⟨i,by unfold P; tauto⟩
  refine ((pr_mono hv.nz hi).trans (pr_exists_le hv.nz _)).trans
    (((Finset.sum_le_sum fun i _=>hk i).trans_eq ?_).trans hB)
  simp [num,mul_assoc]

theorem one_gauze_calendar (r M : ℕ) {s0 : ℕ} (h : OneUnaryParameters p M K s0)
    (ε δ : ℝ) (he : 0<ε) (hd : 0<δ) :
    ∀ᶠ n : ℕ in atTop,let N:=M*n;∀ (m : Mixer p n) (u : Wgt (OneUnit p n N)),
      IsLaw u → oneBySide u m (bp ((1/32:ℝ)*n)) →
      Fintype.card (Row p n)+2*p.h+3≤N → unaryGood m K s0 →
      ∀ Y : OneSilhouette p N r,
        pr u (fun o=>¬oneGauze p ε δ Y m K o)≤bp (-(1/100:ℝ)*n) := by
  classical
  filter_upwards [one_silken p r M h ε δ he hd,
    pay_nat (a:=1/20-1/32) (b:=1/100) 2 (by norm_num)]
    with n hn ht N m u hu hc hN hm Y
  let P (o : OneOrient p n N):=¬oneSmoothSilk p ε δ Y m K o
  let Q (i : Bool) (o : OneUnit p n N):=P (o i)
  have hf (i) : pr u (Q i)≤bp (-((1/20:ℝ)-1/32)*n) := by
    change pr u (fun o=>P (o i))≤_
    rw [←mapW_pr]
    exact (pr_cap (hc i) P).trans ((mul_le_mul_of_nonneg_left
      (hn m hN hm Y) (bp_pos _).le).trans_eq (by rw [←bp_add]; congr 1; ring))
  have hx o (ho : ¬oneGauze p ε δ Y m K o) : ∃ i,Q i o:=Classical.not_forall.mp ho
  rw [two_mul] at ht
  refine ((pr_mono hu.nz hx).trans ((pr_exists_le hu.nz _).trans ?_))
  rw [Fintype.sum_bool]
  exact (add_le_add (hf _) (hf _)).trans ht

end
end Lax793645Proofs.Simplifications
