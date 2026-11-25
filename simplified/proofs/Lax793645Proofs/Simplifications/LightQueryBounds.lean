import Lax793645Proofs.Simplifications.UniformHitBounds
import Lax793645Proofs.Simplifications.AffineQueryHistograms

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis Template Finset Matrix Function Filter Real
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {I : Type} [Fintype I] [DecidableEq I]

/-- Repeated hits alone give small-set and tail bounds for every input
flag. No net of the flagged densities is constructed. -/
theorem light_query_controls (v : Template p I) (M : ℕ) (hM : 1≤M)
    (Y : Type) [Fintype Y] (C η : ℝ) (hC : 0≤C) (hη : 0<η) :
    ∃ δ R : ℝ,0<δ ∧ 0<R ∧ ∀ᶠ n : ℕ in atTop,
      let N:=M*n
      ∀ (m : Mixer p n),2*num (Full p n)<N →
      ∀ μ : Wgt (UnitType p n N),IsLaw μ →
      (∀ o,μ o≤bp (C*N)*pairW (raw m N) (raw m N) o) →
      ∀ κ : I→Wgt (Knobs p.g n),(∀ i,IsLaw (κ i)) →
      (∀ i,mapW (κ i) (freePart p)=unif) →
      ∀ f : UnitType p n N→Inputs p n I→Y,
      let Q:=fromFlags μ (prodW κ) f v.resultKey
      ∀ P : Keys (p:=p) v.t N→Prop,
        (∀ x,hung Q P x → SubLaw x ∧ lsupp x (unifOn P)) ∧
          smallSet (hung Q P) (unifOn P) δ η ∧
          rosterTail (hung Q P) (unifOn P) R η := by
  obtain ⟨B,a,hB,ha,_,hcal⟩:=uniform_hit_calendar v M hM C hC
  have hB0 : 0<B:=by linarith only [hB]
  let δ:=η/(2*B)
  have hδ : 0<δ:=div_pos hη (by positivity)
  have hv : Tendsto (fun n : ℕ=>bp (-a*n)) atTop (nhds 0):=
    (bp_tendsto_zero ha).comp tendsto_natCast_atTop_atTop
  have he : Tendsto (fun n : ℕ=>bp (-10*n)) atTop (nhds 0):=
    (bp_tendsto_zero (by norm_num : (0:ℝ)<10)).comp tendsto_natCast_atTop_atTop
  have hτ : Tendsto (fun n : ℕ=>2*B*bp (-a*n)+bp (-10*n)) atTop (nhds 0) := by
    simpa only [mul_zero,add_zero] using (hv.const_mul (2*B)).add he
  refine ⟨δ,δ⁻¹,hδ,inv_pos.mpr hδ,?_⟩
  filter_upwards [hcal,hv.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1/4)),
    hτ.eventually (eventually_le_nhds (half_pos hη))]
    with n hn hnq hnτ N m hN μ hμ hcap κ hκ hZ f Q P
  let X:=prodW κ
  let K:=v.resultKey (n:=n) (N:=N)
  let u:=colored μ X f
  let q:=coloredP X f K
  have hX : IsLaw X:=prodW_law hκ
  have hu:=colored_ultra hμ hX K f
  have hset:=query_setwise_from_tails v μ hμ κ hκ B (bp (-a*n)) (bp (-10*n))
    hB0.le (bp_pos _) (by linarith only [hnq]) (bp_pos _).le (hn m hN μ hμ hcap κ hκ hZ)
  have hmix : mixW u q=mixW μ (fun o=>v.heatMap o κ):=colored_mixture μ X hX K f
  have hcat (x) (hx : Q x) : catalog u q x := by
    obtain ⟨F,rfl⟩:=hx
    exact flag_catalog K f F hX hμ
  have hsub (x) (hx : Q x) : SubLaw x:=hu.cat_sub x (hcat x hx)
  have hsmall : smallSet Q unif δ η := by
    intro x hx S hS
    have h0:=pr_mono_left (hu.cat_dom x (hcat x hx)).2 S
    rw [hmix] at h0
    have h1:=hset S
    have h2:=mul_le_mul_of_nonneg_left hS hB0.le
    have he : B*δ=η/2:=by dsimp only [δ]; field_simp
    rw [he] at h2
    linarith only [h0,h1,h2,hnτ]
  refine ⟨?_,hung_small Q P δ η hsmall,hung_tail Q P hsub δ η hδ hsmall⟩
  rintro x ⟨y,hy,rfl⟩
  refine ⟨subLaw_sub (hsub y hy) P,fun k hk=>?_⟩
  have he:=density_hung P (subW y P) (subW_carried y P) k
  exact left_ne_zero_of_mul (he.symm ▸ hk)

variable {q : Format} {d : Rates} {side : Bool}

theorem affine_light_certificate (w : Quill p q d side) (t : Tagging p (Messenger q))
    (z : Messenger q→F) (M : ℕ) (hM : 1≤M) (hp : 1≤p.r) (C : ℝ) (hC : 0≤C)
    (hw : w.moral t z) (η : ℝ) (hη : 0<η) :
    ∃ δ R : ℝ,0<δ ∧ 0<R ∧ ∀ᶠ n : ℕ in atTop,
      let N:=M*n
      ∀ (m : Mixer p n) (s : Charts p n d) (μ : Wgt (UnitType p n N))
        (pin : Pin p n N) (K : ℕ),2*num (Full p n)<N → IsLaw μ →
        (∀ o,μ o≤bp (C*N)*PreparationParameters.usual p m N o) →
        let Q:=AffineOptions.custom w μ s t z m pin K
        let ν:=lawNu p N t z
        (∀ x,Q x → SubLaw x ∧ lsupp x ν) ∧ smallSet Q ν δ η ∧ rosterTail Q ν R η := by
  obtain ⟨δ,R,hδ,hR,hcal⟩:=light_query_controls (w.pen t) M hM Bool C η hC hη
  refine ⟨δ,R,hδ,hR,?_⟩
  filter_upwards [hcal,eventually_ge_atTop (2*p.r)] with n hn hnage N m s μ pin K hN hμ hcap
  let κ:=w.policies t z n
  have hκ i : IsLaw (κ i):=Appearance.witLaw (w.allure_apt t z hw i) hp hnage
  exact hn m hN μ hμ hcap κ hκ (fun i=>scopedZ_bit p n _ _ _ (hκ i))
    (AffineOptions.billboard w s t z m pin K) (ownPart t z)

theorem ordinary_light_certificate (w : Quill p q d side) (t : Tagging p (Messenger q))
    (z : Messenger q→F) (M : ℕ) (hM : 1≤M) (hp : 1≤p.r) (C : ℝ) (hC : 0≤C)
    (hw : w.moral t z) (η : ℝ) (hη : 0<η) :
    ∃ δ R : ℝ,0<δ ∧ 0<R ∧ ∀ᶠ n : ℕ in atTop,
      let N:=M*n
      ∀ (m : Mixer p n) (s : Charts p n d) (μ : Wgt (UnitType p n N)),
        2*num (Full p n)<N → IsLaw μ →
        (∀ o,μ o≤bp (C*N)*PreparationParameters.usual p m N o) →
        let Q:=w.custom μ s t z m
        let ν:=lawNu p N t z
        (∀ x,Q x → SubLaw x ∧ lsupp x ν) ∧ smallSet Q ν δ η ∧ rosterTail Q ν R η := by
  obtain ⟨δ,R,hδ,hR,hcal⟩:=light_query_controls (w.pen t) M hM Bool C η hC hη
  refine ⟨δ,R,hδ,hR,?_⟩
  filter_upwards [hcal,eventually_ge_atTop (2*p.r)] with n hn hnage N m s μ hN hμ hcap
  let κ:=w.policies t z n
  have hκ i : IsLaw (κ i):=Appearance.witLaw (w.allure_apt t z hw i) hp hnage
  exact hn m hN μ hμ hcap κ hκ (fun i=>scopedZ_bit p n _ _ _ (hκ i))
    (w.billboard s t z m) (ownPart t z)

end
end Lax793645Proofs.Simplifications
