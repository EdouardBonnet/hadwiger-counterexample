import Lax793645Proofs.Simplifications.QueryLinearEnergy
import Lax793645Proofs.Simplifications.LinearDensityRefinement

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
theorem query_all_filters_linear_partition (v : Template p I) [DecidableEq (KeySlots p v.t)]
    (M : ℕ) (hM : 1≤M) (c L ε : ℝ) (hL : 0<L) (hε : 0<ε) :
    ∃ R : ℕ,∀ᶠ n : ℕ in atTop,
      ∀ (m : Mixer p n),2*num (Full p n)<(M*n:ℕ) →
      ∀ (π : Wgt (UnitType p n (M*n))),IsLaw π →
      (∀ o,π o≤bp (c*(M*n:ℕ))*pairW (raw m (M*n)) (raw m (M*n)) o) →
      ∀ (w : I→Wgt (Knobs p.g n)),(∀ i,IsLaw (w i)) →
      (∀ i,mapW (w i) (freePart p)=unif) →
      (∀ x,prodW w x≤L*unif x) → ∀ (q : I→F) (χ : Inputs p n I→A),
      let K:=queryReferenceSet v q (M*n); let ν:=unifOn K
      let μ:=colored π (prodW w) (queryFlags v χ)
      let d:=coloredCutDensities ν (prodW w) (queryFlags v χ) (templateKeyCoordinates v) K
      ∃ r : ℕ,r≤R ∧ ∃ P : Mat (Fin r) (Fin (M*n)×Bool×KeySlots p v.t),
        ∀ t : Wgt (UnitType p n (M*n)×(A×(I→F))),
        (∀ i,0≤t i) → (∀ i,t i≤μ i) →
        lcost ν (mixW t d) (banner ν P.mulVec (mixW t d))≤ε := by
  obtain ⟨B,_,hE⟩:=query_linear_energy_calendar (Y:=A×(I→F)) v M hM c
  obtain ⟨D,hD⟩:=all_filters_linear_partition (num (A×(I→F))*B+1) ε hε
  obtain ⟨k,hk⟩:=query_density_refinement (A:=A) v M hM c L (ε/2) hL (half_pos hε)
  refine ⟨D*k,?_⟩
  filter_upwards [hE (D*k),hk] with n hn hl m hN π hπ hcap w hw hz hinput q χ K ν μ d
  obtain ⟨hν,henergy⟩:=hn m hN π hπ hcap w hw hz q (queryFlags v χ)
  have hμ : IsLaw μ:=(colored_ultra hπ (prodW_law hw) (templateKeyCoordinates v) (queryFlags v χ)).law
  apply hD _ _ ν μ d hν.sub hμ.sub k (fun r hr P=>(henergy r hr P).1)
  intro r _ P W hW
  obtain ⟨s,hs,R,hR⟩:=hl m hN q (prodW w) π (prodW_law hw) hπ hcap hinput χ r P W hW
  exact ⟨r+s,Nat.add_le_add_left hs r,Fin.append P R,
    (fun x=>fun i : Fin r=>x (i.castAdd s)),append_refines P R,hR⟩

/-- The bound on the projected densities precedes the approximation
accuracy. This keeps the later overlap error proportional to that accuracy. -/
theorem query_bounded_linear_partition (v : Template p I) [DecidableEq (KeySlots p v.t)]
    (M : ℕ) (hM : 1≤M) (c L : ℝ) (hL : 0<L) :
    ∃ B : ℝ,1≤B ∧ ∀ ε : ℝ,0<ε → ∃ R : ℕ,∀ᶠ n : ℕ in atTop,
      ∀ (m : Mixer p n),2*num (Full p n)<(M*n:ℕ) →
      ∀ (π : Wgt (UnitType p n (M*n))),IsLaw π →
      (∀ o,π o≤bp (c*(M*n:ℕ))*pairW (raw m (M*n)) (raw m (M*n)) o) →
      ∀ (w : I→Wgt (Knobs p.g n)),(∀ i,IsLaw (w i)) →
      (∀ i,mapW (w i) (freePart p)=unif) →
      (∀ x,prodW w x≤L*unif x) → ∀ (q : I→F) (χ : Inputs p n I→A),
      let K:=queryReferenceSet v q (M*n); let ν:=unifOn K
      let μ:=colored π (prodW w) (queryFlags v χ)
      let d:=coloredCutDensities ν (prodW w) (queryFlags v χ) (templateKeyCoordinates v) K
      ∃ r : ℕ,r≤R ∧ ∃ P : Mat (Fin r) (Fin (M*n)×Bool×KeySlots p v.t),
        ∀ t : Wgt (UnitType p n (M*n)×(A×(I→F))),
        (∀ i,0≤t i) → (∀ i,t i≤μ i) →
        (∀ x,0≤banner ν P.mulVec (mixW t d) x ∧ banner ν P.mulVec (mixW t d) x≤B) ∧
        lcost ν (mixW t d) (banner ν P.mulVec (mixW t d))≤ε := by
  obtain ⟨B,hB,hE⟩:=query_linear_energy_calendar (Y:=A×(I→F)) v M hM c
  refine ⟨B+1,by linarith,fun ε hε=>?_⟩
  obtain ⟨R,hR⟩:=query_all_filters_linear_partition (A:=A) v M hM c L ε hL hε
  refine ⟨R,?_⟩
  filter_upwards [hR,hE R] with n hn he m hN π hπ hcap w hw hz hinput q χ K ν μ d
  obtain ⟨r,hr,P,hP⟩:=hn m hN π hπ hcap w hw hz hinput q χ
  refine ⟨r,hr,P,fun t ht htc=>?_⟩
  exact ⟨((he m hN π hπ hcap w hw hz q (queryFlags v χ)).2 r hr P).2 t ht htc,hP t ht htc⟩

end
end Lax793645Proofs.Simplifications
