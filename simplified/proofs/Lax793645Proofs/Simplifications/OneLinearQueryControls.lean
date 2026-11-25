import Lax793645Proofs.Simplifications.OneUnfilteredApproximation
import Lax793645Proofs.Simplifications.BoundedApproximationTails
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.HistogramBounds

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Function Filter
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {I Y : Type} [Fintype I] [DecidableEq I] [Fintype Y]

/-- Bounded linear approximations supply both small-set control and a
fixed clipping height, for every flag on the original query experiment. -/
theorem one_linear_query_controls (v : Template p I) [DecidableEq (KeySlots p v.t)]
    (M : ℕ) (hM : 1≤M) (C L : ℝ) (hL : 0<L) :
    ∃ R : ℝ,0<R ∧ ∀ η : ℝ,0<η → ∃ δ : ℝ,0<δ ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (m : Mixer p n),Fintype.card (Row p n)+2*p.h+3≤M*n →
      ∀ μ : Wgt (OneUnit p n (M*n)),IsLaw μ →
      (∀ o,μ o≤bp (C*(M*n:ℕ))*oneUnitRaw m (M*n) o) →
      ∀ κ : I→Wgt (Knobs p.g n),(∀ i,IsLaw (κ i)) →
      (∀ i,mapW (κ i) (freePart p)=unif) →
      (∀ x,prodW κ x≤L*unif x) →
      ∀ (f : OneUnit p n (M*n)→Inputs p n I→Y) (q : I→F),
      let Q:=hung (fromFlags μ (prodW κ) f (oneResultKey v)) (oneOwnKeyPart v.t q)
      let ν:=oneLawNu p (M*n) v.t q
      (∀ x,Q x → SubLaw x ∧ lsupp x ν) ∧
        smallSet Q ν δ η ∧ rosterTail Q ν R η := by
  obtain ⟨B,hB,hcal⟩:=one_unfiltered_bounded_approximation v M hM C L hL
  have hB0 : 0<B:=by linarith only [hB]
  refine ⟨2*B,by positivity,fun η hη=>?_⟩
  let δ:=η/(2*B)
  have hδ : 0<δ:=div_pos hη (by positivity)
  refine ⟨δ,hδ,?_⟩
  filter_upwards [hcal (η/2) (half_pos hη)]
    with n hn m hN μ hμ hcap κ hκ hZ hinput f q Q ν
  let X:=prodW κ
  let K:=oneResultKey v (n:=n) (N:=M*n)
  let P:=oneOwnKeyPart v.t q (N:=M*n)
  let W:=subW (mixW μ (fun o=>oneHeatMap v o κ)) P
  have hX : IsLaw X:=prodW_law hκ
  obtain ⟨g,hg,he⟩:=hn m hN μ hμ hcap κ hκ hZ hinput q
  have hu:=colored_ultra hμ hX K f
  have hcat (x) (hx : fromFlags μ X f K x) :
      catalog (colored μ X f) (coloredP X f K) x := by
    obtain ⟨F,rfl⟩:=hx
    exact flag_catalog K f F hX hμ
  have hbase (x) (hx : fromFlags μ X f K x) : SubLaw x ∧
      ∀ k,x k≤mixW μ (fun o=>oneHeatMap v o κ) k := by
    refine ⟨hu.cat_sub x (hcat x hx),?_⟩
    have hh:=(hu.cat_dom x (hcat x hx)).2
    rw [colored_mixture μ X hX K f] at hh
    exact hh
  have hsub (x) (hx : Q x) : SubLaw x := by
    obtain ⟨y,hy,rfl⟩:=hx
    exact subLaw_sub (hbase y hy).1 P
  have hdom (x) (hx : Q x) : ∀ k,x k≤W k := by
    obtain ⟨y,hy,rfl⟩:=hx
    exact fun k=>mul_le_mul_of_nonneg_right ((hbase y hy).2 k) (ind_nonneg (P k))
  have hsupp (x) (hx : Q x) : lsupp x ν := by
    obtain ⟨y,hy,rfl⟩:=hx
    intro k hk
    exact uniform_on_support P k (by
      by_contra hh
      exact hk (by change y k*ind (P k)=0; rw [ind_zero hh,mul_zero]))
  have hW : lsupp W ν := by
    intro k hk
    exact uniform_on_support P k (by
      by_contra hh
      exact hk (by simp [W,subW,ind_zero hh]))
  have hb x (hx : Q x) := dominated_approximation_tails ν W g
    (unifOn_sub P).nz hW B (η/2) (fun k=>(hg k).2) he x (hsub x hx).nz (hdom x hx)
  refine ⟨fun x hx=>⟨hsub x hx,hsupp x hx⟩,?_,?_⟩
  · intro x hx S hS
    have hh:=mul_le_mul_of_nonneg_left hS hB0.le
    have heq : B*δ=η/2:=by dsimp only [δ]; field_simp
    rw [heq] at hh
    linarith only [(hb x hx).1 S,hh]
  · intro x hx
    simpa only [mul_div_cancel₀ _ (by norm_num : (2:ℝ)≠0)] using (hb x hx).2

end
end Lax793645Proofs.Simplifications
