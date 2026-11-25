import Lax793645Proofs.Simplifications.OneQueryLinearEnergy
import Lax793645Proofs.Simplifications.QueryFourierSpectrum

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function Filter
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I A : Type} [Fintype I] [DecidableEq I] [Fintype A] [Nonempty A] {p : Shape}

/-- One bounded linear partition per capped leaf approximates every
fractional filter on its nominal and actual parity statuses. The filter
is selected after the partition and may depend on another leaf. -/
theorem one_query_all_filters_linear_partition (v : Template p I) [DecidableEq (KeySlots p v.t)]
    (M : ℕ) (hM : 1≤M) (c L ε : ℝ) (hL : 0<L) (hε : 0<ε) :
    ∃ R : ℕ,∀ᶠ n : ℕ in atTop,
      ∀ (m : Mixer p n),Fintype.card (Row p n)+2*p.h+3≤M*n →
      ∀ (π : Wgt (OneUnit p n (M*n))),IsLaw π →
      (∀ o,π o≤bp (c*(M*n:ℕ))*oneUnitRaw m (M*n) o) →
      ∀ (w : I→Wgt (Knobs p.g n)),(∀ i,IsLaw (w i)) →
      (∀ i,mapW (w i) (freePart p)=unif) →
      (∀ x,prodW w x≤L*unif x) → ∀ (q : I→F) (χ : Inputs p n I→A),
      let K:=oneQueryReferenceSet v q (M*n); let ν:=unifOn K
      let μ:=colored π (prodW w) (oneQueryFlags v χ)
      let d:=coloredCutDensities ν (prodW w) (oneQueryFlags v χ) (oneTemplateCoordinates v) K
      ∃ r : ℕ,r≤R ∧ ∃ P : Mat (Fin r) (Fin (M*n)×Bool×KeySlots p v.t),
        ∀ t : Wgt (OneUnit p n (M*n)×(A×(I→F))),
        (∀ i,0≤t i) → (∀ i,t i≤μ i) →
        lcost ν (mixW t d) (banner ν P.mulVec (mixW t d))≤ε := by
  let E := crowded (ownPort v.t)
  let κ := bp (-quadraticReferenceCost E)/2
  have hκ : 0 < κ := half_pos (bp_pos _)
  let η := κ*ε/8
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨δ,hδ,hcomp⟩ := one_capped_input_status_comparison (A:=A) v M hM c L η hL hη
  obtain ⟨k,hk⟩ := exists_nat_gt (1/δ^2)
  have hk' : 1 ≤ (k:ℝ)*δ^2 := ((div_lt_iff₀ (sq_pos_of_pos hδ)).mp hk).le
  let τ := κ*ε/(4*2^k)
  have hτ : 0 < τ := by dsimp [τ]; positivity
  obtain ⟨B,hB,hE⟩ := one_query_linear_energy_calendar (Y:=A×(I→F)) v M hM c L hL
  let V := num (A×(I→F))*B+1
  obtain ⟨R,hR⟩ := exists_nat_gt (V/(κ*τ^2))
  have hM' : 0 < (M:ℝ)/2 := by
    exact div_pos (by exact_mod_cast Nat.zero_lt_one.trans_le hM) (by norm_num)
  have hlim : Tendsto (fun n : ℕ => bp (-((M*n:ℕ):ℝ)/2)) atTop (nhds 0) := by
    convert (bp_tendsto_zero hM').comp tendsto_natCast_atTop_atTop using 1
    funext n
    congr 1
    push_cast
    ring
  have hlim' : Tendsto (fun n : ℕ => 2*bp (quadraticReferenceCost E) *
      bp (-((M*n:ℕ):ℝ)/2) * 2^k) atTop (nhds 0) := by
    simpa using (hlim.const_mul (2*bp (quadraticReferenceCost E))).mul_const ((2:ℝ)^k)
  refine ⟨R,?_⟩
  filter_upwards [hE R,hcomp,hlim.eventually (eventually_le_nhds hκ),
    hlim'.eventually (eventually_le_nhds hδ)] with n hn hc hm hb mixer hN π hπ hcap w hw hz hinput q χ K ν μ d
  let hflag := oneQueryFlags (N:=M*n) v χ
  have hμ : IsLaw μ := (colored_ultra hπ (prodW_law hw) (oneTemplateCoordinates v) hflag).law
  obtain ⟨hν,henergy⟩ := hn mixer hN π hπ hcap w hw hz hinput q hflag
  let Z := geoMatrix (ownPort v.t) (ownMap v.t q)
  obtain ⟨_,hmass,hbias⟩ := quadratic_reference_bias E Z hm
  change κ ≤ pr unif K at hmass
  let γ := 2*bp (quadraticReferenceCost E)*bp (-((M*n:ℕ):ℝ)/2)
  apply spectrum_all_filters K (hκ.trans_le hmass) hν μ hμ.sub d η τ δ γ V ε
    hδ hτ (mul_nonneg (mul_nonneg (by norm_num) (bp_pos _).le) (bp_pos _).le) k R hk' hb
  · have hr := (div_lt_iff₀ (mul_pos hκ (sq_pos_of_pos hτ))).mp hR
    calc V < κ*((R:ℝ)*τ^2) := by linarith only [hr]
         _ ≤ _ := mul_le_mul_of_nonneg_right hmass (by positivity)
  · exact fun P => (henergy R le_rfl P).1
  · exact hbias
  · intro t ht htc D hD hsup hFour
    obtain ⟨G,hG,hrep⟩ := colored_filter_representation
      (B:=KeyCoordinates (KeySlots p v.t) (M*n)) π hπ (prodW w) (prodW_law hw) hflag t ht htc
    rw [hrep (oneTemplateCoordinates v) ν K (fun x hx => uniform_on_support K x hx)]
    have htest := hc mixer hN q D (prodW w) (fun _ => 1) π hπ hcap hD hsup hFour
      (fun _ => by norm_num) (prodW_law hw).nz hinput χ (fun o a b => G o (a,b))
      (fun o a b => by rw [abs_of_nonneg (hG o (a,b)).1]; exact (hG o (a,b)).2)
    have hs x : D x*ind (K x) = D x := by
      by_cases h : D x = 0
      · simp [h]
      rw [ind_one (hsup x h),mul_one]
    simp_rw [hs]
    exact (abs_avg_le hπ.nz).trans (by simpa only [hflag,oneQueryFlags,mul_one] using htest)
  · calc 2*(2*η+2^k*τ) = κ*ε := by dsimp only [η,τ]; field_simp; ring
         _ ≤ _ := mul_le_mul_of_nonneg_right hmass hε.le

/-- The bound on the projected densities precedes the approximation
accuracy. This keeps the later overlap error proportional to that accuracy. -/
theorem one_query_bounded_linear_partition (v : Template p I) [DecidableEq (KeySlots p v.t)]
    (M : ℕ) (hM : 1≤M) (c L : ℝ) (hL : 0<L) :
    ∃ B : ℝ,1≤B ∧ ∀ ε : ℝ,0<ε → ∃ R : ℕ,∀ᶠ n : ℕ in atTop,
      ∀ (m : Mixer p n),Fintype.card (Row p n)+2*p.h+3≤M*n →
      ∀ (π : Wgt (OneUnit p n (M*n))),IsLaw π →
      (∀ o,π o≤bp (c*(M*n:ℕ))*oneUnitRaw m (M*n) o) →
      ∀ (w : I→Wgt (Knobs p.g n)),(∀ i,IsLaw (w i)) →
      (∀ i,mapW (w i) (freePart p)=unif) →
      (∀ x,prodW w x≤L*unif x) → ∀ (q : I→F) (χ : Inputs p n I→A),
      let K:=oneQueryReferenceSet v q (M*n); let ν:=unifOn K
      let μ:=colored π (prodW w) (oneQueryFlags v χ)
      let d:=coloredCutDensities ν (prodW w) (oneQueryFlags v χ) (oneTemplateCoordinates v) K
      ∃ r : ℕ,r≤R ∧ ∃ P : Mat (Fin r) (Fin (M*n)×Bool×KeySlots p v.t),
        ∀ t : Wgt (OneUnit p n (M*n)×(A×(I→F))),
        (∀ i,0≤t i) → (∀ i,t i≤μ i) →
        (∀ x,0≤banner ν P.mulVec (mixW t d) x ∧ banner ν P.mulVec (mixW t d) x≤B) ∧
        lcost ν (mixW t d) (banner ν P.mulVec (mixW t d))≤ε := by
  obtain ⟨B,hB,hE⟩:=one_query_linear_energy_calendar (Y:=A×(I→F)) v M hM c L hL
  refine ⟨B+1,by linarith,fun ε hε=>?_⟩
  obtain ⟨R,hR⟩:=one_query_all_filters_linear_partition (A:=A) v M hM c L ε hL hε
  refine ⟨R,?_⟩
  filter_upwards [hR,hE R] with n hn he m hN π hπ hcap w hw hz hinput q χ K ν μ d
  obtain ⟨r,hr,P,hP⟩:=hn m hN π hπ hcap w hw hz hinput q χ
  refine ⟨r,hr,P,fun t ht htc=>?_⟩
  exact ⟨((he m hN π hπ hcap w hw hz hinput q (oneQueryFlags v χ)).2 r hr P).2 t ht htc,hP t ht htc⟩

end
end Lax793645Proofs.Simplifications
