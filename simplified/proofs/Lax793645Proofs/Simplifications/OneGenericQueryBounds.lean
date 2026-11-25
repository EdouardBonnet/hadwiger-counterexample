import Lax793645Proofs.Simplifications.ReducedOptions
import Lax793645Proofs.Simplifications.OneFiniteDualSystems
import Lax793645Proofs.Simplifications.OneLinearComparisonCalendar
namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis StatusAnalysis.Appearance StatusAnalysis.DualAnalysis OneAppearance Filter Finset Matrix Function LinearMap Module Template
open scoped BigOperators Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {p : Shape} {n N K M r s0 : ℕ} {d : Rates}
def oneGenericSmoothSilk (p : Shape) (ε δ:ℝ) (Y:OneSilhouette p N r)
    (m:Mixer p n) (K:ℕ) (o:OneOrient p n N) :=
    ∀ x : Appearance p,x.f=Flavor.full→
      (x.apt → oneClose x Y o ε) ∧ oneFoil x Y o m K δ
def oneGenericGauze (p : Shape) (ε δ:ℝ) (Y:OneSilhouette p N r)
    (m:Mixer p n) (K:ℕ) (o:OneUnit p n N) :=
  ∀ i,oneGenericSmoothSilk p ε δ Y m K (o i)
theorem one_generic_silken (p : Shape) (r M : ℕ) (h : OneUnaryParameters p M K s0)
    (ε δ : ℝ) (he:0<ε) (hd:0<δ) :
    ∀ᶠ n : ℕ in atTop, let N:=M*n; ∀ m : Mixer p n,Fintype.card (Row p n)+2*p.h+3≤N →
      unaryGood m K s0 → ∀ Y: OneSilhouette p N r,
      pr (oneRaw m N) (fun i=>¬oneGenericSmoothSilk p ε δ Y m K i)≤bp (-(1/20:ℝ)*n) := by
  classical
  let A:= {x : Appearance p // x.f=Flavor.full}
  filter_upwards [eventually_all.mpr (fun x:A=>OneAppearance.oneFoilCap x.val r M h δ hd),
    eventually_all.mpr (fun x:A=>OneAppearance.oneReadCap x.val r M h ε he),
    pay_nat (a:=1/18) (b:=1/20) (num A*2) (by norm_num)] with n hn ht hB N m hN hM Y
  let v:=oneRaw m N
  have hv : IsLaw v:=one_raw_law (N:=N) m (by omega)
  let P (x:A) (o:OneOrient p n N) :=
    (x.val.apt ∧ ¬oneClose x.val Y o ε)∨ ¬oneFoil x.val Y o m K δ
  have hk (x : A) : pr v (P x) ≤ 2*bp (-(1/18:ℝ)*n) := by
    rw [two_mul]; apply (pr_or_le hv.nz).trans
    refine add_le_add ((ht x m hN Y).trans (bp_le ?_)) (hn x m hN hM Y)
    linarith [(Nat.cast_nonneg n :0≤(n:ℝ))]
  have hi o (h : ¬oneGenericSmoothSilk p ε δ Y m K o) : ∃ i, P i o := by
    unfold oneGenericSmoothSilk at h
    push Not at h
    obtain ⟨i,hi,h⟩:=h
    exact ⟨⟨i,hi⟩,by unfold P; tauto⟩
  refine ((pr_mono hv.nz hi).trans (pr_exists_le hv.nz _)).trans
    (((Finset.sum_le_sum fun i _=>hk i).trans_eq ?_).trans hB)
  simp [num,mul_assoc]

theorem one_generic_gauze_calendar (r M : ℕ) {s0 : ℕ} (h : OneUnaryParameters p M K s0)
    (ε δ : ℝ) (he : 0<ε) (hd : 0<δ) :
    ∀ᶠ n : ℕ in atTop,let N:=M*n;∀ (m : Mixer p n) (u : Wgt (OneUnit p n N)),
      IsLaw u → oneBySide u m (bp ((1/32:ℝ)*n)) →
      Fintype.card (Row p n)+2*p.h+3≤N → unaryGood m K s0 →
      ∀ Y : OneSilhouette p N r,
        pr u (fun o=>¬oneGenericGauze p ε δ Y m K o)≤bp (-(1/100:ℝ)*n) := by
  classical
  filter_upwards [one_generic_silken p r M h ε δ he hd,
    pay_nat (a:=1/20-1/32) (b:=1/100) 2 (by norm_num)]
    with n hn ht N m u hu hc hN hm Y
  let P (o : OneOrient p n N):=¬oneGenericSmoothSilk p ε δ Y m K o
  let Q (i : Bool) (o : OneUnit p n N):=P (o i)
  have hf (i) : pr u (Q i)≤bp (-((1/20:ℝ)-1/32)*n) := by
    change pr u (fun o=>P (o i))≤_
    rw [←mapW_pr]
    exact (pr_cap (hc i) P).trans ((mul_le_mul_of_nonneg_left
      (hn m hN hm Y) (bp_pos _).le).trans_eq (by rw [←bp_add]; congr 1; ring))
  have hx o (ho : ¬oneGenericGauze p ε δ Y m K o) : ∃ i,Q i o:=Classical.not_forall.mp ho
  rw [two_mul] at ht
  refine ((pr_mono hu.nz hx).trans ((pr_exists_le hu.nz _).trans ?_))
  rw [Fintype.sum_bool]
  exact (add_le_add (hf _) (hf _)).trans ht

namespace OneAppearance
variable (x : Appearance p) (Y : OneSilhouette p N r)
variable {d : ℕ}
set_option maxHeartbeats 800000 in
theorem oneGenericDemonstrates (o : OneUnit p n N) {m : Mixer p n}
    (v : Ax p n d) (K:ℕ) (i:Nodes) (j:Fin r) (δ : ℝ) (hd:0<δ)
    (z : Digest p.g) (u:Cell d)
    (he : z.feasible x.l x.f) (hf : z.sumBit=x.q) (ht : 1≤p.r) (hn : 2*p.r≤n)
    (hh : δ≤ oneReference x Y j)
    (hfull : x.f=Flavor.full) (hs : oneGenericSmoothSilk p δ δ Y m K (o i)) (hK : d≤K^2)
    (hV : Injective v) (hv : ∀ x,totalRank (v x) ≤ K) :
    basebeta p K/2 ≤ pr (oneReflected x Y i o m v j) (nearly p z (z.diagO,u)) := by
  classical
  have ha : x.apt := ⟨z,he,hf⟩
  let μ:= oneReference x Y j
  let f := o i
  obtain ⟨hM,hB⟩:= hs x hfull
  specialize hM ha
  specialize hB z j he hf hh
  let U (y:OneAtomKey (p:=p) (x.trot.t ()) N) := Y x.l x.q y=j
  have hm : basebeta p K*μ ≤
      pr (x.wit n) (fun y=> (scan p x.l x.f y=z∧Y x.l x.q (oneFace x f y)=j) ∧
        stains x.trot m v y=u) := by
    let h := one_patrol_beta x.trot U m K z he ht hn f
    dsimp only at h
    rw [hf] at h
    exact h hB d hK v hV hv u
  let w := nearly p z (z.diagO,u)
  have hq (y : Knobs p.g n) :
      (scan p x.l x.f y=z ∧ Y x.l x.q (oneFace x f y)=j) ∧ stains x.trot m v y=u →
        oneShowTag x Y (o i) y=j∧ w (oneProfile x i o m v y) := by
    rintro ⟨⟨h,h1⟩,h2⟩
    refine ⟨h1,h,?_⟩; rw [oneSmudges,h,h2]
  have hW := Appearance.witLaw ha ht hn
  have heq := (hm.trans (pr_mono hW.nz hq)).trans_eq (oneShow_pr x Y i o m v hW j w)
  let ν:= oneEmpirical x Y f j
  have h2 : ν ≤ 2*μ := by
    have hz : |μ-ν|≤δ := le_trans
      (Finset.single_le_sum (fun k _ => abs_nonneg (oneReference x Y k-oneEmpirical x Y f k))
        (Finset.mem_univ j)) hM
    change δ≤ μ at hh
    linarith [(abs_le.mp hz).1]
  let Q := pr (oneReflected x Y i o m v j) w
  have h3 : basebeta p K*μ≤ ν*Q := heq
  have ht := mul_le_mul_of_nonneg_right h2
    (show 0≤ Q from pr_nonneg (oneReflectedLaw x Y hW i o m v j).nz)
  apply le_of_mul_le_mul_right _ (hd.trans_le hh)
  change _*μ ≤ Q*μ
  linarith only [h3,ht]

end OneAppearance

theorem one_generic_plume_reports (p:Shape) (K :ℕ) (m:Mixer p n) (Y:OneSilhouette p N r)
    (s : ImagePlan (Comp p.g) (OneColumn p n)) (t:Charts p n d) (o:OneUnit p n N)
    (hs:oneCharted t s) (hh:∀ i,d i≤K^2) (h:imagePlanRank s≤K)
    (hg:3≤p.g) (hp:1≤p.r) (hn:2*p.r≤n) (δ:ℝ) (hδ:0<δ)
    (hY:oneGenericGauze p δ δ Y m K o):
    reports p r (oneWisp p Y) (oneWake p Y m o t) (basebeta p K/2) δ := by
  constructor
  · intro i x hx k; exact oneReflectedLaw x Y (Appearance.witLaw hx hp hn) _ _ _ _ _
  · intro i x hx k; exact oneRefInk x Y _ _ _ _ _
  intro i x hx he k hk v
  obtain ⟨g,ha,hb,hc⟩:=generic_summary p hg x.l x.q v.1
  rw [←hx] at ha
  have hf:= oneGenericDemonstrates x Y o (m:=m) (t i) K i k δ hδ g v.2 ha hb hp hn hk hx (hY _)
    (hh _) (hs i).2 (fun x=>le_trans (one_effective_rank s i _ (by rw [←(hs i).1]; exact mem_range_self _ _)) h)
  exact hf.trans (pr_mono (oneReflectedLaw x Y (Appearance.witLaw he hp hn) i o m (t i) k).nz
    (fun j hj=>hj.2.trans (Prod.ext hc rfl)))

namespace OneQuill
variable {q : Format} {d : Rates} {b : Bool}
def oneGeneric (w : Quill p q d b) : Prop:=∀ i,w.flav i=Flavor.full

theorem one_generic_gauze_area (w : Quill p q d b) (t : Tagging p (Messenger q))
    (z : Messenger q→F) (hw : w.moral t z) (hfull : oneGeneric w)
    (Y : OneSilhouette p N r) (o : OneUnit p n N) (m : Mixer p n) (δ η : ℝ)
    (h : oneGenericGauze p δ η Y m K o) : oneMatchesArea w t z Y o δ :=
  fun i=>(h (parcel b i) (w.allure t z i) (hfull i)).1 (w.allure_apt t z hw i)
end OneQuill

def oneGenericOption {q : Format} {d e : Rates} (w : Typus p q d e) : Prop :=
  OneQuill.oneGeneric w.qA ∧ OneQuill.oneGeneric w.qB

def oneGenericPermission {q : Format} {d e : Rates} (w : Typus p q d e) : Prop :=
  onePermission w ∧ oneGenericOption w
end
end Lax793645Proofs.Simplifications
