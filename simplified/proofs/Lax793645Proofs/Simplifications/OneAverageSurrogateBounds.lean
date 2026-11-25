import Lax793645Proofs.Simplifications.OneSurrogateOverlap

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis Finset Function
open scoped Classical BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {p : Shape} {n N r R : ℕ} {q : Format} {d e : Rates} {b : Bool}
variable {Λ : Type} [Fintype Λ]

def oneLeafOfSide (j : Bool) (l : Λ×Λ):=if j then l.1 else l.2

theorem one_leaf_average (μ : Wgt Λ) (hμ : IsLaw μ) (j : Bool) (f : Wgt Λ) :
    avg (pairW μ μ) (fun l=>f (oneLeafOfSide j l))=avg μ f := by
  cases j <;> simp only [oneLeafOfSide,Bool.false_eq_true,if_false,if_true,pairW_avg,hμ.avg_const]

namespace OneQuill

/-- The exceptional mass is measured in the mixed population. The
acceptance filter may depend on both independently drawn leaves. -/
theorem one_average_projected_error (w : Quill p q d b)
    (t : Tagging p (Messenger q)) (z : Messenger q→F)
    (μ : Wgt Λ) (hμ : IsLaw μ) (π : Λ→Wgt (OneUnit p n N)) (hπ : ∀ l,IsLaw (π l))
    (j : Bool) (P : Λ×Λ→OneUnit p n N→Prop) (a : Λ→Charts p n d)
    (m : Mixer p n) (Y : OneSilhouette p N r)
    (L : KeyCoordinates (KeySlots p t) N→ₗ[F]Vec (Fin R))
    (hκ : ∀ i,IsLaw (w.policies t z n i)) (hν : IsLaw (oneLawNu p N t z))
    (Z : OneUnit p n N→Prop) {ε : ℝ} (hε : 0≤ε)
    (htest : ∀ (l : Λ×Λ) (φ : Wgt (Vec (Fin R))),(∀ x,|φ x|≤1) →
      ∀ o,P l o → ¬Z o →
      |oneProwl w t z o m (a (oneLeafOfSide j l)) (φ ∘ L.comp (oneKeyCoordinatesMap t N))-
        oneSheen w t z o m (a (oneLeafOfSide j l)) Y (φ ∘ L.comp (oneKeyCoordinatesMap t N))|≤ε) :
    avg (pairW μ μ) (fun l=>
      varOne (mapW (oneDisplayCoordinates w t z (π (oneLeafOfSide j l)) (P l) m
        (a (oneLeafOfSide j l)) Y) L)
        (mapW (oneSales w t z (π (oneLeafOfSide j l)) (P l) m (a (oneLeafOfSide j l))) L))≤
      ε+2*pr (mixW μ π) Z := by
  have hi (l : Λ×Λ):=one_coordinate_projected_error w t z (π (oneLeafOfSide j l)) (P l)
    m (a (oneLeafOfSide j l)) Y L (hπ _) hκ hν Z hε (htest l)
  have he : avg (pairW μ μ) (fun l=>ε+2*pr (π (oneLeafOfSide j l)) Z)=
      ε+2*pr (mixW μ π) Z := by
    rw [avg_add,(pairW_law hμ hμ).avg_const,avg_mul',
      one_leaf_average μ hμ j (fun k=>pr (π k) Z)]
    congr 2
    exact (mixW_avg μ π (fun x=>ind (Z x))).symm
  exact (avg_mono (pairW_law hμ hμ).nz hi).trans_eq he

end OneQuill

namespace OneTypus
variable (w : Typus p q d e) (μ : Wgt Λ) (π : Λ→Wgt (OneUnit p n N))
    (F G : Λ×Λ→OneUnit p n N→Prop) (a : Λ→Charts p n d) (a' : Λ→Charts p n e)
    (m : Mixer p n) (Y : OneSilhouette p N r)

/-- Small actual common-projection overlap and small table-comparison
error force small expected numerical score. All quantities are finite. -/
theorem one_average_score_bound {A : Type} [Fintype A]
    (P : KeyCoordinates (KeySlots p w.t) N→A)
    (hμ : IsLaw μ) (hπ : ∀ l,IsLaw (π l))
    (ha : ∀ i,IsLaw (w.qA.policies w.t w.z n i))
    (hb : ∀ i,IsLaw (w.qB.policies w.t w.z n i))
    (hν : IsLaw (unifOn (oneOwnPart (N:=N) w.t w.z)))
    (hN : 2*num (Messenger q×Toast p)+2≤(N:ℝ))
    (ε C D : ℝ) (hε : 0≤ε)
    (hC : let ν:=unifOn (oneOwnPart (N:=N) w.t w.z)
      avg (pairW μ μ) (fun l=>dip ν
        (banner ν P (density ν (oneSales w.qA w.t w.z (π l.1) (F l) m (a l.1))))
        (banner ν P (density ν (oneSales w.qB w.t w.z (π l.2) (G l) m (a' l.2)))))≤C)
    (hD : avg (pairW μ μ) (fun l=>
      varOne (mapW (OneQuill.oneDisplayCoordinates w.qA w.t w.z (π l.1) (F l) m (a l.1) Y) P)
        (mapW (oneSales w.qA w.t w.z (π l.1) (F l) m (a l.1)) P)+
      varOne (mapW (OneQuill.oneDisplayCoordinates w.qB w.t w.z (π l.2) (G l) m (a' l.2) Y) P)
        (mapW (oneSales w.qB w.t w.z (π l.2) (G l) m (a' l.2)) P))≤D)
    (hsmall : C+D≤(ε/2)^2)
    (href : 2*quadraticNetFact (trayPort p w.t)*bp (-(N:ℝ)/2)≤ε/2) :
    avg (pairW μ μ) (fun l=>oneFilteredScore w (π l.1) (π l.2) (F l) (G l)
      (a l.1) (a' l.2) m Y)≤ε := by
  let V:=pairW μ μ
  let f (l : Λ×Λ):=oneFilteredScore w (π l.1) (π l.2) (F l) (G l) (a l.1) (a' l.2) m Y
  let g (l : Λ×Λ):=dip (oneLawNu p N w.t w.z)
    (OneQuill.oneShowcase w.qA w.t w.z (π l.1) (F l) m (a l.1) Y)
    (OneQuill.oneShowcase w.qB w.t w.z (π l.2) (G l) m (a' l.2) Y)
  have hsq : avg V (fun l=>g l^2)≤C+D := by
    have hi (l : Λ×Λ):=one_projected_surrogate_mend w (π l.1) (π l.2) (F l) (G l)
      (a l.1) (a' l.2) m Y P (hπ _) (hπ _) ha hb hν
    have hh:=avg_mono (pairW_law hμ hμ).nz hi
    rw [avg_add] at hh
    exact hh.trans (add_le_add hC hD)
  have hmean:=(mean_sq V (pairW_law hμ hμ) g).trans (hsq.trans hsmall)
  have hgap : avg V f-avg V g≤ε/2 := by
    rw [←avg_sub]
    apply (pairW_law hμ hμ).avg_le
    intro l
    exact (le_abs_self _).trans
      ((one_filtered_shine w (π l.1) (π l.2) (F l) (G l) (a l.1) (a' l.2) m Y
        (hπ _) (hπ _) ha hb hN).trans href)
  change avg V f≤ε
  nlinarith only [hmean,hgap,hε]

end OneTypus
end
end Lax793645Proofs.Simplifications
