import Lax793645Proofs.Simplifications.OneLinearQueryTestComparison
import Lax793645Proofs.Simplifications.ProjectedDensityMend

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis Finset Function
open scoped Classical BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N r : ℕ} {q : Format} {d e : Rates} {b : Bool}

namespace OneQuill
variable (w : Quill p q d b) (t : Tagging p (Messenger q)) (z : Messenger q→F)
  (μ : Wgt (OneUnit p n N)) (P : OneUnit p n N→Prop)
  (m : Mixer p n) (s : Charts p n d) (Y : OneSilhouette p N r)

def oneShowcase : Wgt (OneKeys t N):=fun k=>avg μ (fun o=>ind (P o)*oneMirror w t z o m s Y k)
def oneDisplayMass : Wgt (OneKeys t N):=fun k=>oneLawNu p N t z k*oneShowcase w t z μ P m s Y k
def oneActualMass : Wgt (OneKeys t N):=mapW (oneSales w t z μ P m s) (oneQueryCoordinateEquiv t N)

theorem one_showcase_bound (hμ : IsLaw μ) (hκ : ∀ i,IsLaw (w.policies t z n i)) :
    bower (oneShowcase w t z μ P m s Y) := by
  constructor
  · intro x
    exact avg_nonneg hμ.nz (fun o=>mul_nonneg (ind_nonneg _) (one_mirror_floor w t z o m s Y hκ x).1)
  · intro x
    exact hμ.avg_le (fun o=>(mul_le_mul (ind_le_one _) (one_mirror_floor w t z o m s Y hκ x).2
      (one_mirror_floor w t z o m s Y hκ x).1 zero_le_one).trans_eq (one_mul _))

theorem one_display_mean (W : Wgt (OneKeys t N)) :
    avg (oneDisplayMass w t z μ P m s Y) W=
      avg μ (fun o=>ind (P o)*oneSheen w t z o m s Y W) := by
  unfold oneDisplayMass oneShowcase oneSheen
  simp only [avg,mul_assoc,sum_mul,mul_sum]
  rw [sum_comm]
  exact sum_congr rfl (fun i _=>sum_congr rfl (fun j _=>by ring))

theorem one_actual_mean (W : Wgt (OneKeys t N)) :
    avg (oneActualMass w t z μ P m s) W=
      avg μ (fun o=>ind (P o)*oneProwl w t z o m s W) := by
  rw [oneActualMass,mapW_avg]
  exact one_sales_prowl w t z m s μ P W

theorem one_prowl_bound (o : OneUnit p n N) (W : Wgt (OneKeys t N))
    (hW : ∀ x,|W x|≤1) (hκ : ∀ i,IsLaw (w.policies t z n i)) :
    |oneProwl w t z o m s W|≤1 := by
  have hstate : IsLaw ((w.pen t).state z n):=prodW_law hκ
  apply (abs_avg_le hstate.nz).trans
  apply hstate.avg_le
  intro x
  rw [abs_mul,abs_of_nonneg (ind_nonneg _)]
  exact (mul_le_mul (hW _) (ind_le_one _) (ind_nonneg _) zero_le_one).trans_eq (one_mul _)

theorem one_sheen_bound (o : OneUnit p n N) (W : Wgt (OneKeys t N))
    (hW : ∀ x,|W x|≤1) (hκ : ∀ i,IsLaw (w.policies t z n i))
    (hν : IsLaw (oneLawNu p N t z)) :
    |oneSheen w t z o m s Y W|≤1 := by
  apply (abs_avg_le hν.nz).trans
  apply hν.avg_le
  intro x
  have hh:=one_mirror_floor w t z o m s Y hκ x
  rw [abs_mul,abs_of_nonneg hh.1]
  exact (mul_le_mul hh.2 (hW _) (abs_nonneg _) zero_le_one).trans_eq (one_mul _)

/-- Exceptional orientations are charged before any pair-dependent
filter is applied, and the accepted measures remain unnormalized. -/
theorem one_display_test (W : Wgt (OneKeys t N)) (hW : ∀ x,|W x|≤1)
    (hμ : IsLaw μ) (hκ : ∀ i,IsLaw (w.policies t z n i))
    (hν : IsLaw (oneLawNu p N t z)) (Z : OneUnit p n N→Prop)
    {ε : ℝ} (hε : 0≤ε)
    (hg : ∀ o,P o → ¬Z o → |oneProwl w t z o m s W-oneSheen w t z o m s Y W|≤ε) :
    |avg (oneDisplayMass w t z μ P m s Y) W-avg (oneActualMass w t z μ P m s) W|≤
      ε+2*pr μ Z := by
  rw [one_display_mean,one_actual_mean,←avg_sub]
  have hp (o : OneUnit p n N) :
      |ind (P o)*oneSheen w t z o m s Y W-ind (P o)*oneProwl w t z o m s W|≤
        ε+2*ind (Z o) := by
    rw [←mul_sub,abs_mul,abs_of_nonneg (ind_nonneg _)]
    by_cases hP : P o
    · rw [ind_one hP,one_mul]
      by_cases hZ : Z o
      · rw [ind_one hZ]
        have h₁:=one_prowl_bound w t z m s o W hW hκ
        have h₂:=one_sheen_bound w t z m s Y o W hW hκ hν
        have h₃:=abs_sub (oneSheen w t z o m s Y W) (oneProwl w t z o m s W)
        linarith
      · rw [ind_zero hZ,mul_zero,add_zero,abs_sub_comm]
        exact hg o hP hZ
    · rw [ind_zero hP,zero_mul]
      exact add_nonneg hε (mul_nonneg (by norm_num) (ind_nonneg _))
  exact (abs_avg_le hμ.nz).trans ((avg_mono hμ.nz hp).trans_eq
    (by rw [avg_add,avg_mul',hμ.avg_const]; rfl))

end OneQuill

namespace OneTypus
variable (w : Typus p q d e) (o o' : OneUnit p n N)
  (s : Charts p n d) (t : Charts p n e) (m : Mixer p n) (Y : OneSilhouette p N r)

def oneChimera (i : Messenger q):=
  dip (oneLawOmega p N (w.t i) (w.z i)) (OneQuill.oneSeraph w.qA w.t w.z o m s Y i)
    (OneQuill.oneSeraph w.qB w.t w.z o' m t Y i)
def oneMomus :=oneKappa (w.qA.pen w.t)*oneKappa (w.qB.pen w.t)
def oneConstellation:=oneMomus w*∏ i,oneChimera w o o' s t m Y i

theorem one_shine_match (ha : ∀ i,IsLaw (w.qA.policies w.t w.z n i))
    (hb : ∀ i,IsLaw (w.qB.policies w.t w.z n i))
    (hN : 2*num (Messenger q×Toast p)+2≤(N:ℝ)) :
    |oneConstellation w o o' s t m Y-
      dip (oneLawNu p N w.t w.z) (OneQuill.oneMirror w.qA w.t w.z o m s Y)
        (OneQuill.oneMirror w.qB w.t w.z o' m t Y)|≤
      2*quadraticNetFact (trayPort p w.t)*bp (-(N:ℝ)/2) := by
  let A:=OneQuill.oneSeraph w.qA w.t w.z o m s Y
  let B:=OneQuill.oneSeraph w.qB w.t w.z o' m t Y
  let C (i : Messenger q):=fun x=>A i x*B i x
  have hc i x : |C i x|≤1 := by
    have h₁:=OneQuill.one_seraph_floor w.qA w.t w.z o m s Y i (ha i) x
    have h₂:=OneQuill.one_seraph_floor w.qB w.t w.z o' m t Y i (hb i) x
    dsimp only [C,A,B]
    rw [abs_mul,abs_of_nonneg h₁.1,abs_of_nonneg h₂.1]
    exact (mul_le_mul h₁.2 h₂.2 h₂.1 zero_le_one).trans_eq (one_mul _)
  have he : dip (oneLawNu p N w.t w.z) (OneQuill.oneMirror w.qA w.t w.z o m s Y)
      (OneQuill.oneMirror w.qB w.t w.z o' m t Y)=
      oneMomus w*avg (oneLawNu p N w.t w.z) (prodW C) := by
    unfold dip
    rw [←avg_mul']
    apply avg_congr
    intro x _
    simp only [OneQuill.oneMirror,oneMomus,prodW,C,A,B,prod_mul_distrib]
    ring
  have hκ : |oneMomus w|≤1 := by
    rw [oneMomus,abs_mul,abs_of_pos (one_kappa_pos _),abs_of_pos (one_kappa_pos _)]
    exact (mul_le_mul (OneQuill.one_kappa_top w.qA w.t) (OneQuill.one_kappa_top w.qB w.t)
      (one_kappa_pos _).le zero_le_one).trans_eq (one_mul _)
  rw [he]
  change |oneMomus w*(∏ i,avg (oneLawOmega p N (w.t i) (w.z i)) (C i))-
    oneMomus w*avg (oneLawNu p N w.t w.z) (prodW C)|≤_
  rw [←mul_sub,abs_mul]
  exact ((mul_le_mul_of_nonneg_right hκ (abs_nonneg _)).trans_eq (one_mul _)).trans
    (by rw [abs_sub_comm]; exact one_reference_product w.t w.z C hc hN)

end OneTypus
end
end Lax793645Proofs.Simplifications
