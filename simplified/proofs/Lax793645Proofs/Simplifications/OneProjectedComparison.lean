import Lax793645Proofs.Simplifications.OneSurrogateAggregation
import Lax793645Proofs.Simplifications.OneLinearComparisonCalendar
import Lax793645Proofs.Simplifications.EquivariantProjection

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis Finset Function
open scoped Classical BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

private theorem uniform_instance_value {A : Type} (i j : Fintype A) (P : A→Prop) (x : A) :
    @unifOn A i P x=@unifOn A j P x := by
  cases Subsingleton.elim i j
  rfl

theorem finite_variation_dual_bound {A : Type} [Fintype A] (p q : Wgt A) (ε : ℝ)
    (h : ∀ f : Wgt A,(∀ x,|f x|≤1) → |avg p f-avg q f|≤ε) : varOne p q≤ε := by
  let f (x : A):=if p x<q x then (-1:ℝ) else 1
  have hf x : |f x|≤1:=by dsimp only [f]; split <;> norm_num
  have he x : (p x-q x)*f x=|p x-q x| := by
    dsimp only [f]
    split
    next hx => rw [abs_of_neg (sub_neg.mpr hx)]; ring
    next hx => rw [abs_of_nonneg (sub_nonneg.mpr (le_of_not_gt hx)),mul_one]
  have hh:=h f hf
  have heq : avg p f-avg q f=varOne p q := by
    simp only [avg,←sum_sub_distrib,←sub_mul,he,varOne]
  rw [heq,abs_of_nonneg (var_nonneg p q)] at hh
  exact hh

variable {p : Shape} {n N r R : ℕ} {q : Format} {d : Rates} {b : Bool}
namespace OneQuill
variable (w : Quill p q d b) (t : Tagging p (Messenger q)) (z : Messenger q→F)
  (μ : Wgt (OneUnit p n N)) (P : OneUnit p n N→Prop)
  (m : Mixer p n) (s : Charts p n d) (Y : OneSilhouette p N r)

def oneDisplayCoordinates : Wgt (KeyCoordinates (KeySlots p t) N):=
  mapW (oneDisplayMass w t z μ P m s Y) (oneQueryCoordinateEquiv t N).symm

theorem one_display_coordinates_value (x : KeyCoordinates (KeySlots p t) N) :
    oneDisplayCoordinates w t z μ P m s Y x=
      unifOn (oneOwnPart t z) x*oneShowcase w t z μ P m s Y (oneQueryCoordinateEquiv t N x) := by
  rw [oneDisplayCoordinates,mapW_equiv_val]
  have hh:=congrFun (one_reference_coordinates (N:=N) t z) x
  rw [mapW_equiv_val] at hh
  convert congrArg (fun a=>a*oneShowcase w t z μ P m s Y (oneQueryCoordinateEquiv t N x)) hh using 1
  all_goals
    apply congrArg (fun a=>a*oneShowcase w t z μ P m s Y (oneQueryCoordinateEquiv t N x))
    try unfold oneLawNu
    exact uniform_instance_value _ _ _ _

theorem one_sales_support : lsupp (oneSales w t z μ P m s) (unifOn (oneOwnPart t z)) := by
  intro x hx
  have hc : oneOwnPart t z x := by
    by_contra hh
    exact hx (subW_carried _ (oneQueryReferenceSet (w.pen t) z N) x hh)
  rw [unifOn_val,ind_one hc]
  have hpos : 0<nbr (oneOwnPart (N:=N) t z) := by
    have hh:=weight_le_tot (fun x=>ind_nonneg (oneOwnPart (N:=N) t z x)) x
    rw [ind_one hc] at hh
    exact lt_of_lt_of_le zero_lt_one hh
  exact div_ne_zero one_ne_zero (ne_of_gt hpos)

theorem one_display_projected_error (L : OneKeys t N→ₗ[F]Vec (Fin R))
    (hμ : IsLaw μ) (hκ : ∀ i,IsLaw (w.policies t z n i))
    (hν : IsLaw (oneLawNu p N t z)) (Z : OneUnit p n N→Prop)
    {ε : ℝ} (hε : 0≤ε)
    (hg : ∀ (φ : Wgt (Vec (Fin R))),(∀ x,|φ x|≤1) →
      ∀ o,P o → ¬Z o → |oneProwl w t z o m s (φ ∘ L)-oneSheen w t z o m s Y (φ ∘ L)|≤ε) :
    varOne (mapW (oneDisplayMass w t z μ P m s Y) L)
      (mapW (oneActualMass w t z μ P m s) L)≤ε+2*pr μ Z := by
  apply finite_variation_dual_bound
  intro φ hφ
  rw [mapW_avg,mapW_avg]
  exact one_display_test w t z μ P m s Y (φ ∘ L) (fun x=>hφ _) hμ hκ hν Z hε (hg φ hφ)

theorem one_coordinate_projected_error
    (L : KeyCoordinates (KeySlots p t) N→ₗ[F]Vec (Fin R))
    (hμ : IsLaw μ) (hκ : ∀ i,IsLaw (w.policies t z n i))
    (hν : IsLaw (oneLawNu p N t z)) (Z : OneUnit p n N→Prop)
    {ε : ℝ} (hε : 0≤ε)
    (hg : ∀ (φ : Wgt (Vec (Fin R))),(∀ x,|φ x|≤1) →
      ∀ o,P o → ¬Z o →
      |oneProwl w t z o m s (φ ∘ L.comp (oneKeyCoordinatesMap t N))-
        oneSheen w t z o m s Y (φ ∘ L.comp (oneKeyCoordinatesMap t N))|≤ε) :
    varOne (mapW (oneDisplayCoordinates w t z μ P m s Y) L)
      (mapW (oneSales w t z μ P m s) L)≤ε+2*pr μ Z := by
  have hh:=one_display_projected_error w t z μ P m s Y (L.comp (oneKeyCoordinatesMap t N))
    hμ hκ hν Z hε hg
  unfold oneDisplayCoordinates
  rw [map_nested]
  have he : ⇑(L.comp (oneKeyCoordinatesMap t N))=L∘(oneQueryCoordinateEquiv t N).symm :=rfl
  rw [he,oneActualMass,map_nested] at hh
  have hi : (L∘(oneQueryCoordinateEquiv t N).symm)∘oneQueryCoordinateEquiv t N=L := by
    funext x
    simp only [Function.comp_apply,Equiv.symm_apply_apply]
  rw [hi] at hh
  exact hh

end OneQuill
end
end Lax793645Proofs.Simplifications
