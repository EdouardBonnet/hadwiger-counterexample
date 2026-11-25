import Lax793645Proofs.Simplifications.OneSupportLinearComparison
import Lax793645Proofs.Simplifications.ProjectedDomination
import Lax793645Proofs.Simplifications.OneSurrogateOverlap

/-! Average support surrogates over unnormalized acceptance filters and bound their projected excess. -/

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Function LinearMap Finset StatusAnalysis Filter
open scoped Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace OneQuill
variable {p : Shape} {n N r : ℕ} {q : Format} {d : Rates} {b : Bool}
variable (w : Quill p q d b) (t : Tagging p (Messenger q)) (z : Messenger q→F)
  (o : OneUnit p n N) (m : Mixer p n) (s : Charts p n d) (Y : OneSilhouette p N r)

def oneSupportShowcase (μ : Wgt (OneUnit p n N)) (P : OneUnit p n N→Prop)
    (θ : ℝ) : Wgt (OneKeys t N):=fun k=>
  avg μ (fun o=>ind (P o)*oneSupportMirror w t z o m s Y θ k)

theorem one_support_showcase_bound (μ : Wgt (OneUnit p n N)) (P : OneUnit p n N→Prop)
    (θ : ℝ) (hθ : 0≤θ ∧ θ≤1) (hμ : IsLaw μ) :
    bower (oneSupportShowcase w t z m s Y μ P θ) := by
  constructor
  · intro x
    exact avg_nonneg hμ.nz (fun o=>mul_nonneg (ind_nonneg _)
      (one_support_mirror_bound w t z o m s Y θ hθ x).1)
  · intro x
    exact hμ.avg_le (fun o=>(mul_le_mul (ind_le_one _)
      (one_support_mirror_bound w t z o m s Y θ hθ x).2
      (one_support_mirror_bound w t z o m s Y θ hθ x).1 zero_le_one).trans_eq (one_mul _))

theorem one_support_mirror_scale (θ : ℝ) (x : OneKeys t N) :
    oneSupportMirror w t z o m s Y θ x=
      θ^Fintype.card (Messenger q)*oneSupportMirror w t z o m s Y 1 x := by
  simp only [oneSupportMirror,prodW,oneSupportSeraph,supportLower,
    one_mul,prod_mul_distrib,prod_const,card_univ]
  ring

theorem one_support_showcase_scale (μ : Wgt (OneUnit p n N)) (P : OneUnit p n N→Prop)
    (θ : ℝ) (x : OneKeys t N) :
    oneSupportShowcase w t z m s Y μ P θ x=
      θ^Fintype.card (Messenger q)*oneSupportShowcase w t z m s Y μ P 1 x := by
  unfold oneSupportShowcase
  simp_rw [one_support_mirror_scale w t z (θ:=θ)]
  rw [←avg_mul']
  exact avg_congr (fun o _=>by ring)

theorem one_support_showcase_mean (μ : Wgt (OneUnit p n N)) (P : OneUnit p n N→Prop)
    (θ : ℝ) (W : Wgt (OneKeys t N)) :
    avg (oneLawNu p N t z) (fun k=>oneSupportShowcase w t z m s Y μ P θ k*W k)=
      avg μ (fun o=>ind (P o)*oneSupportSheen w t z o m s Y θ W) := by
  unfold oneSupportShowcase oneSupportSheen
  simp only [avg,mul_assoc,sum_mul,mul_sum]
  rw [sum_comm]
  exact sum_congr rfl (fun i _=>sum_congr rfl (fun j _=>by ring))

theorem one_support_sheen_bound (θ : ℝ) (hθ : 0≤θ ∧ θ≤1) (W : Wgt (OneKeys t N))
    (hW : ∀ x,|W x|≤1) (hν : IsLaw (oneLawNu p N t z)) :
    |oneSupportSheen w t z o m s Y θ W|≤1 := by
  apply (abs_avg_le hν.nz).trans
  apply hν.avg_le
  intro x
  have hh:=one_support_mirror_bound w t z o m s Y θ hθ x
  rw [abs_mul,abs_of_nonneg hh.1]
  exact (mul_le_mul hh.2 (hW _) (abs_nonneg _) zero_le_one).trans_eq (one_mul _)

theorem one_support_display_test (μ : Wgt (OneUnit p n N)) (P : OneUnit p n N→Prop)
    (θ : ℝ) (hθ : 0≤θ ∧ θ≤1) (W : Wgt (OneKeys t N))
    (hW : ∀ x,0≤W x ∧ W x≤1) (hμ : IsLaw μ)
    (hκ : ∀ i,IsLaw (w.policies t z n i)) (hν : IsLaw (oneLawNu p N t z))
    (Z : OneUnit p n N→Prop) {ε : ℝ} (hε : 0≤ε)
    (hg : ∀ o,P o → ¬Z o → oneSupportSheen w t z o m s Y θ W-
      oneProwl w t z o m s W≤ε) :
    avg (oneLawNu p N t z) (fun k=>oneSupportShowcase w t z m s Y μ P θ k*W k)-
      avg (oneSales w t z μ P m s) (W ∘ oneQueryCoordinateEquiv t N)≤ε+2*pr μ Z := by
  rw [one_support_showcase_mean,one_sales_prowl,←avg_sub]
  have hW' x : |W x|≤1:=by rw [abs_of_nonneg (hW x).1]; exact (hW x).2
  have hp (o : OneUnit p n N) :
      ind (P o)*oneSupportSheen w t z o m s Y θ W-ind (P o)*oneProwl w t z o m s W≤
        ε+2*ind (Z o) := by
    rw [←mul_sub]
    by_cases hP : P o
    · rw [ind_one hP,one_mul]
      by_cases hZ : Z o
      · rw [ind_one hZ,mul_one]
        have h₁:=one_prowl_bound w t z m s o W hW' hκ
        have h₂:=one_support_sheen_bound w t z o m s Y θ hθ W hW' hν
        linarith only [(abs_le.mp h₁).1,(abs_le.mp h₂).2,hε]
      · rw [ind_zero hZ,mul_zero,add_zero]
        exact hg o hP hZ
    · rw [ind_zero hP,zero_mul]
      exact add_nonneg hε (mul_nonneg (by norm_num) (ind_nonneg _))
  exact (avg_mono hμ.nz hp).trans_eq (by rw [avg_add,avg_mul',hμ.avg_const]; rfl)

def oneSupportProjectedLoss {A : Type} [Fintype A]
    (μ : Wgt (OneUnit p n N)) (P : OneUnit p n N→Prop) (θ : ℝ)
    (L : KeyCoordinates (KeySlots p t) N→A) : ℝ:=
  let ν:=unifOn (oneOwnPart (N:=N) t z)
  avg ν (fun x=>max
    (banner ν L (oneSupportShowcase w t z m s Y μ P θ ∘ oneQueryCoordinateEquiv t N) x-
      banner ν L (density ν (oneSales w t z μ P m s)) x) 0)

theorem one_support_projected_error {R : ℕ}
    (μ : Wgt (OneUnit p n N)) (P : OneUnit p n N→Prop) (θ : ℝ) (hθ : 0≤θ ∧ θ≤1)
    (L : KeyCoordinates (KeySlots p t) N→ₗ[F]Vec (Fin R))
    (hμ : IsLaw μ) (hκ : ∀ i,IsLaw (w.policies t z n i))
    (hν : IsLaw (oneLawNu p N t z))
    (hν' : IsLaw (unifOn (oneOwnPart (N:=N) t z))) (Z : OneUnit p n N→Prop)
    {ε : ℝ} (hε : 0≤ε)
    (hg : ∀ (φ : Wgt (Vec (Fin R))),(∀ x,0≤φ x ∧ φ x≤1)→
      ∀ o,P o→¬Z o→
      oneSupportSheen w t z o m s Y θ (φ ∘ L.comp (oneKeyCoordinatesMap t N))-
        oneProwl w t z o m s (φ ∘ L.comp (oneKeyCoordinatesMap t N))≤ε) :
    oneSupportProjectedLoss w t z m s Y μ P θ L≤ε+2*pr μ Z := by
  apply projected_excess_test_bound _ hν' L
    (oneSupportShowcase w t z m s Y μ P θ ∘ oneQueryCoordinateEquiv t N)
    (oneSales w t z μ P m s) (one_sales_support w t z μ P m s)
  intro φ hφ
  let W:=φ ∘ L.comp (oneKeyCoordinatesMap t N)
  have hh:=one_support_display_test w t z m s Y μ P θ hθ W (fun x=>hφ _) hμ hκ hν Z hε (hg φ hφ)
  have he : W ∘ oneQueryCoordinateEquiv t N=φ ∘ L := by
    funext x
    change φ (L ((oneQueryCoordinateEquiv t N).symm (oneQueryCoordinateEquiv t N x)))=φ (L x)
    rw [Equiv.symm_apply_apply]
  rw [he] at hh
  have ht : avg (fun x=>unifOn (oneOwnPart t z) x*
      (oneSupportShowcase w t z m s Y μ P θ ∘ oneQueryCoordinateEquiv t N) x) (φ ∘ L)=
      avg (oneLawNu p N t z) (fun k=>oneSupportShowcase w t z m s Y μ P θ k*W k) := by
    have hi:=one_reference_integral t z
      (fun x=>(oneSupportShowcase w t z m s Y μ P θ ∘ oneQueryCoordinateEquiv t N) x*(φ ∘ L) x)
    simpa only [avg,Function.comp_apply,Equiv.apply_symm_apply,mul_assoc,W,
      LinearMap.comp_apply,oneKeyCoordinatesMap,LinearMap.coe_mk,AddHom.coe_mk] using hi
  rw [ht]
  exact hh

end OneQuill

end
end Lax793645Proofs.Simplifications
