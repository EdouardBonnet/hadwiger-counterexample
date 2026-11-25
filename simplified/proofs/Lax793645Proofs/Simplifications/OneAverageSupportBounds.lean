import Lax793645Proofs.Simplifications.OneSupportOverlap
import Lax793645Proofs.Simplifications.OneAverageSurrogateBounds

/-! Average over independent leaves before imposing filters that may depend on both leaves. -/

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Function LinearMap Finset StatusAnalysis Filter
open scoped Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

section
variable {p : Shape} {n N r R : ℕ} {q : Format} {d e : Rates} {b : Bool}
variable {Λ : Type} [Fintype Λ]
namespace OneQuill

theorem one_average_support_error (w : Quill p q d b)
    (t : Tagging p (Messenger q)) (z : Messenger q→F)
    (μ : Wgt Λ) (hμ : IsLaw μ) (π : Λ→Wgt (OneUnit p n N)) (hπ : ∀ l,IsLaw (π l))
    (j : Bool) (P : Λ×Λ→OneUnit p n N→Prop) (a : Λ→Charts p n d)
    (m : Mixer p n) (Y : OneSilhouette p N r) (θ : ℝ) (hθ : 0≤θ ∧ θ≤1)
    (L : KeyCoordinates (KeySlots p t) N→ₗ[F]Vec (Fin R))
    (hκ : ∀ i,IsLaw (w.policies t z n i)) (hν : IsLaw (oneLawNu p N t z))
    (hν' : IsLaw (unifOn (oneOwnPart (N:=N) t z)))
    (Z : OneUnit p n N→Prop) {ε : ℝ} (hε : 0≤ε)
    (htest : ∀ (l : Λ×Λ) (φ : Wgt (Vec (Fin R))),(∀ x,0≤φ x ∧ φ x≤1)→
      ∀ o,P l o→¬Z o→
      oneSupportSheen w t z o m (a (oneLeafOfSide j l)) Y θ (φ ∘ L.comp (oneKeyCoordinatesMap t N))-
        oneProwl w t z o m (a (oneLeafOfSide j l)) (φ ∘ L.comp (oneKeyCoordinatesMap t N))≤ε) :
    avg (pairW μ μ) (fun l=>oneSupportProjectedLoss w t z m
      (a (oneLeafOfSide j l)) Y (π (oneLeafOfSide j l)) (P l) θ L)≤ε+2*pr (mixW μ π) Z := by
  have hi (l : Λ×Λ):=one_support_projected_error w t z m (a (oneLeafOfSide j l)) Y
    (π (oneLeafOfSide j l)) (P l) θ hθ L (hπ _) hκ hν hν' Z hε (htest l)
  have he : avg (pairW μ μ) (fun l=>ε+2*pr (π (oneLeafOfSide j l)) Z)=ε+2*pr (mixW μ π) Z := by
    rw [avg_add,(pairW_law hμ hμ).avg_const,avg_mul',one_leaf_average μ hμ j (fun k=>pr (π k) Z)]
    congr 2
    exact (mixW_avg μ π (fun x=>ind (Z x))).symm
  exact (avg_mono (pairW_law hμ hμ).nz hi).trans_eq he

end OneQuill

namespace OneTypus
variable (w : Typus p q d e) (μ : Wgt Λ) (π : Λ→Wgt (OneUnit p n N))
    (F G : Λ×Λ→OneUnit p n N→Prop) (a : Λ→Charts p n d) (a' : Λ→Charts p n e)
    (m : Mixer p n) (Y : OneSilhouette p N r) (θ : ℝ)

theorem one_average_support_score_bound {A : Type} [Fintype A]
    (P : KeyCoordinates (KeySlots p w.t) N→A) (hθ : 0<θ ∧ θ≤1)
    (hμ : IsLaw μ) (hπ : ∀ l,IsLaw (π l))
    (hν : IsLaw (unifOn (oneOwnPart (N:=N) w.t w.z)))
    (hN : 2*num (Messenger q×Toast p)+2≤(N:ℝ))
    (ε C D : ℝ) (hε : 0≤ε)
    (hC : let ν:=unifOn (oneOwnPart (N:=N) w.t w.z)
      avg (pairW μ μ) (fun l=>dip ν
        (banner ν P (density ν (oneSales w.qA w.t w.z (π l.1) (F l) m (a l.1))))
        (banner ν P (density ν (oneSales w.qB w.t w.z (π l.2) (G l) m (a' l.2)))))≤C)
    (hD : avg (pairW μ μ) (fun l=>
      OneQuill.oneSupportProjectedLoss w.qA w.t w.z m (a l.1) Y (π l.1) (F l) θ P+
      OneQuill.oneSupportProjectedLoss w.qB w.t w.z m (a' l.2) Y (π l.2) (G l) θ P)≤D)
    (hsmall : C+D≤((θ^Fintype.card (Messenger q))^2*(ε/2))^2)
    (href : 2*quadraticNetFact (trayPort p w.t)*bp (-(N:ℝ)/2)≤ε/2) :
    avg (pairW μ μ) (fun l=>oneSupportFilteredScore w (π l.1) (π l.2) (F l) (G l)
      (a l.1) (a' l.2) m Y)≤ε := by
  let V:=pairW μ μ
  let H:=(θ^Fintype.card (Messenger q))^2
  have hH : 0<H:=sq_pos_of_pos (pow_pos hθ.1 _)
  let f (l : Λ×Λ):=oneSupportFilteredScore w (π l.1) (π l.2) (F l) (G l) (a l.1) (a' l.2) m Y
  let g (l : Λ×Λ):=dip (oneLawNu p N w.t w.z)
    (OneQuill.oneSupportShowcase w.qA w.t w.z m (a l.1) Y (π l.1) (F l) θ)
    (OneQuill.oneSupportShowcase w.qB w.t w.z m (a' l.2) Y (π l.2) (G l) θ)
  have hsq : avg V (fun l=>g l^2)≤C+D := by
    have hi (l : Λ×Λ):=one_support_projected_mend w (π l.1) (π l.2) (F l) (G l)
      (a l.1) (a' l.2) m Y θ P ⟨hθ.1.le,hθ.2⟩ (hπ _) (hπ _) hν
    have hh:=avg_mono (pairW_law hμ hμ).nz hi
    rw [avg_add] at hh
    exact hh.trans (add_le_add hC hD)
  have hmean:=(mean_sq V (pairW_law hμ hμ) g).trans (hsq.trans hsmall)
  have hmean' : avg V g≤H*(ε/2) := by
    change (avg V g)^2≤(H*(ε/2))^2 at hmean
    nlinarith only [hmean,mul_nonneg hH.le (div_nonneg hε (by norm_num : (0:ℝ)≤2))]
  have hgap : H*avg V f-avg V g≤H*(ε/2) := by
    rw [←avg_mul',←avg_sub]
    apply (pairW_law hμ hμ).avg_le
    intro l
    have hshine:=(le_abs_self _).trans
      ((one_filtered_support_shine w (π l.1) (π l.2) (F l) (G l) (a l.1) (a' l.2) m Y
        (hπ _) (hπ _) hN).trans href)
    have hcover:=one_support_overlap_scale w (π l.1) (π l.2) (F l) (G l)
      (a l.1) (a' l.2) m Y θ
    have hh:=mul_le_mul_of_nonneg_left hshine hH.le
    change H*_≤g l at hcover
    dsimp only [f]
    linarith only [hh,hcover]
  change avg V f≤ε
  nlinarith only [hgap,hmean',hH]

end OneTypus
end

end
end Lax793645Proofs.Simplifications
