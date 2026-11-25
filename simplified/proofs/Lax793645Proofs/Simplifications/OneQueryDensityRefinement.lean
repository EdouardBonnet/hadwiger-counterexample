import Lax793645Proofs.Simplifications.OneCappedInputStatusComparison
import Lax793645Proofs.Simplifications.QueryDensityRefinement
import Lax793645Proofs.Simplifications.FilteredColoredDensities
import Lax793645Proofs.Simplifications.LinearPartitionAppend

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function Filter
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I A : Type} [Fintype I] [DecidableEq I] [Fintype A] [Nonempty A]
  {p : Shape} {n N : ℕ}

def oneQueryFlags (v : Template p I) (χ : Inputs p n I→A)
    (o : OneUnit p n N) (x : Inputs p n I) : A×(I→F):=(χ x,oneQueryPValues v o x)

def oneQueryReferenceSet (v : Template p I) (q : I→F) (N : ℕ) :
    KeyCoordinates (KeySlots p v.t) N→Prop :=
  fun x=>oneOwnPart v.t q x

/-- Each bounded discrepancy witness can be replaced by its conditional
average on a bounded linear refinement. This controls every subweight of
the orientation/status law simultaneously. -/
theorem one_query_density_refinement (v : Template p I) [DecidableEq (KeySlots p v.t)]
    (M : ℕ) (hM : 1≤M) (c L ε : ℝ) (hL : 0<L) (hε : 0<ε) :
    ∃ k : ℕ,∀ᶠ n : ℕ in atTop,
      ∀ (m : Mixer p n),Fintype.card (Row p n)+2*p.h+3 ≤ M*n →
      ∀ (q : I→F) (κ : Wgt (Inputs p n I)) (π : Wgt (OneUnit p n (M*n))),
      IsLaw κ → IsLaw π →
      (∀ o,π o≤bp (c*(M*n:ℕ))*oneUnitRaw m (M*n) o) →
      (∀ x,κ x≤L*unif x) → ∀ χ : Inputs p n I→A,
      let K:=oneQueryReferenceSet v q (M*n); let ν:=unifOn K
      let μ:=colored π κ (oneQueryFlags v χ)
      let d:=coloredCutDensities ν κ (oneQueryFlags v χ) (oneTemplateCoordinates v) K
      ∀ (r : ℕ) (P : Mat (Fin r) (Fin (M*n)×Bool×KeySlots p v.t))
        (W : Wgt (KeyCoordinates (KeySlots p v.t) (M*n))),
      (∀ x,|W x|≤1) →
      ∃ s : ℕ,s≤k ∧ ∃ R : Mat (Fin s) (Fin (M*n)×Bool×KeySlots p v.t),
        ∀ t : Wgt (OneUnit p n (M*n)×(A×(I→F))),
        (∀ i,0≤t i) → (∀ i,t i≤μ i) →
        |dip ν (mixW t d) (fun x=>W x-banner ν (Matrix.mulVec (Fin.append P R)) W x)|≤ε := by
  obtain ⟨δ,hδ,hcal⟩:=one_capped_input_status_comparison (A:=A) v M hM c L (ε/2) hL (half_pos hε)
  obtain ⟨k,hk⟩:=linear_supported_refinement 1 (2*δ) zero_le_one (by positivity)
  refine ⟨k,?_⟩
  filter_upwards [hcal] with n hn m hN q κ π hκ hπ hcap hinput χ K ν μ d r P W hW
  obtain ⟨s,hs,R,hS,hFour⟩:=hk _ _ K W P.mulVec hW
  refine ⟨s,hs,R,fun t ht htcap=>?_⟩
  let S:=banner ν (fun x=>(P*ᵥx,R*ᵥx)) W
  let D (x : KeyCoordinates (KeySlots p v.t) (M*n)):=(W x-S x)*ind (K x)/2
  have hD x : |D x|≤1:=by
    dsimp only [D]
    rw [abs_div,abs_mul,abs_of_nonneg (ind_nonneg _)]
    norm_num only [abs_of_pos (by norm_num : (0:ℝ)<2)]
    apply (div_le_one (by norm_num : (0:ℝ)<2)).mpr
    have hh : |W x-S x|≤2:=(abs_sub _ _).trans (by linarith only [hW x,hS x])
    exact (mul_le_mul_of_nonneg_right hh (ind_nonneg _)).trans
      ((mul_le_mul_of_nonneg_left (ind_le_one _) (by norm_num)).trans_eq (by ring))
  have hsup x (hx : D x≠0) : K x:=by
    by_contra h
    exact hx (by simp [D,ind_zero h])
  have hF ξ : |linearFourier D ξ|≤δ:=by
    have he : linearFourier D ξ=linearFourier (fun x=>(W x-S x)*ind (K x)) ξ/2:=by
      unfold linearFourier D
      rw [←avg_div]
      apply avg_congr
      intro x _
      ring
    rw [he,abs_div]
    norm_num only [abs_of_pos (by norm_num : (0:ℝ)<2)]
    apply (div_le_iff₀ (by norm_num : (0:ℝ)<2)).mpr
    exact (hFour ξ).trans_eq (mul_comm _ _)
  obtain ⟨F,hFbound,hrep⟩:=colored_filter_representation
    (B:=KeyCoordinates (KeySlots p v.t) (M*n)) π hπ κ hκ (oneQueryFlags v χ) t ht htcap
  have hcomp:=hn m hN q D κ (fun _=>1) π hπ hcap hD hsup hF
    (fun _=>by norm_num) hκ.nz hinput χ (fun o a b=>F o (a,b))
    (fun o a b=>by rw [abs_of_nonneg (hFbound o (a,b)).1]; exact (hFbound o (a,b)).2)
  rw [banner_append]
  change |dip ν (mixW t d) (fun x=>W x-S x)|≤ε
  rw [hrep (oneTemplateCoordinates v) ν K (fun x hx=>uniform_on_support K x hx)]
  have he o : avg κ (fun x=>(W (oneTemplateCoordinates v o x)-S (oneTemplateCoordinates v o x))*
      ind (K (oneTemplateCoordinates v o x))*F o (oneQueryFlags v χ o x))=
      2*avg κ (fun x=>D (oneTemplateCoordinates v o x)*1*F o (χ x,oneQueryPValues v o x)) := by
    rw [←avg_mul']
    apply avg_congr
    intro x _
    dsimp only [D,oneQueryFlags]
    ring
  simp_rw [he,avg_mul',abs_mul]
  norm_num only [abs_of_pos (by norm_num : (0:ℝ)<2)]
  exact (mul_le_mul_of_nonneg_left ((abs_avg_le hπ.nz).trans hcomp) (by norm_num)).trans_eq (by ring)

end
end Lax793645Proofs.Simplifications
