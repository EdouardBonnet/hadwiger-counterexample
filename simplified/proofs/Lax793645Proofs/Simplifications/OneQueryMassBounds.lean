import Lax793645Proofs.Simplifications.OneStation

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis Finset Function
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem input_histogram_zero {A X T : Type} [Fintype A] [Fintype X] [Fintype T]
    (key:A→X→T) (μ:Wgt X) (ρ:Wgt A) (U:A→X→Prop) (h:∀ a x,¬U a x) :
    inputHistogram key μ ρ U=0 := by
  funext k
  unfold inputHistogram
  have hp a : (fun x=>U a x ∧ key a x=k)=(fun _=>False):=
    funext fun x=>propext ⟨fun hx=>h a x hx.1,False.elim⟩
  simp_rw [hp,pr_false]
  simp

namespace OneQuill
variable {p:Shape} {n N K:ℕ} {q:Format} {d:Rates} {b:Bool}

theorem one_sales_zero (w:Quill p q d b) (t:Tagging p (Messenger q)) (z:Messenger q→F)
    (μ:Wgt (OneUnit p n N)) (P:OneUnit p n N→Prop) (m:Mixer p n) (s:Charts p n d)
    (h:∀ o,¬P o) : oneSales w t z μ P m s=0 := by
  have hh : mapW (oneSales w t z μ P m s) (oneQueryCoordinateEquiv t N)=0:=
    (one_sales_histogram w t z μ P m s).trans
      (input_histogram_zero _ _ _ _ (fun x o hx=>h o hx.1))
  funext k
  have hk:=congrFun hh (oneQueryCoordinateEquiv t N k)
  simpa only [mapW_equiv_val,Equiv.symm_apply_apply,Pi.zero_apply] using hk

theorem one_good_sales_zero (w:Quill p q d b) (t:Tagging p (Messenger q)) (z:Messenger q→F)
    (pin:ImagePlan (Comp p.g) (OneColumn p n)) (K:ℕ)
    (μ:Wgt (OneUnit p n N)) (P:OneUnit p n N→Prop) (m:Mixer p n) (s:Charts p n d)
    (h:∀ o,¬P o) : oneGoodSales w t z pin K μ P m s=0 := by
  have hh : oneGoodHistogram w t z pin K μ P m s=0:=
    input_histogram_zero _ _ _ _ (fun x o hx=>h o hx.2.1)
  unfold oneGoodSales
  rw [hh]
  funext k
  simp [mapW_equiv_val]

end OneQuill

namespace OneStation
variable {p:Shape} {n N K:ℕ} {q:Format} {d e:Rates} {pop:OneLeafMixture p n N}
    (v:OneStation p n N K pop)

theorem sales_rejection (w:Typus p q d e) (m:Mixer p n) (μ:Wgt (OneUnit p n N))
    (i j:pop.T) (k:Fin (2^oneDeckMax p K))
    (hu:IsLaw (partW μ i.val)) (hv:IsLaw (partW μ j.val))
    (hκA:∀ z,IsLaw (w.qA.policies w.t w.z n z))
    (hκB:∀ z,IsLaw (w.qB.policies w.t w.z n z)) :
    let A:=oneSales w.qA w.t w.z (partW μ i.val) (v.frontPage w m i j k) m (v.cAxes i d)
    let B:=oneSales w.qB w.t w.z (partW μ j.val) (v.backPage w m i j k) m (v.cAxes j e)
    (∀ x,0≤v.leftSales w m μ i j k x ∧ v.leftSales w m μ i j k x≤A x) ∧
    (∀ x,0≤v.rightSales w m μ i j k x ∧ v.rightSales w m μ i j k x≤B x) ∧
    varOne A (v.leftSales w m μ i j k)≤bp (num (Messenger q)+oneBaseProtectionDim p K-n) ∧
    varOne B (v.rightSales w m μ i j k)≤bp (num (Messenger q)+oneBaseProtectionDim p K-n) := by
  intro A B
  by_cases h:v.news w i j k
  · obtain ⟨hA,hvarA⟩:=OneQuill.one_good_sales_rejection w.qA w.t w.z (pop.pin i.val).sp K
      (partW μ i.val) (v.frontPage w m i j k) m (v.cAxes i d) hu.sub h.2.1.2.1 hκA
    obtain ⟨hB,hvarB⟩:=OneQuill.one_good_sales_rejection w.qB w.t w.z (pop.pin j.val).sp K
      (partW μ j.val) (v.backPage w m i j k) m (v.cAxes j e) hv.sub h.2.2.2.1 hκB
    exact ⟨hA,hB,hvarA,hvarB⟩
  · have hF o : ¬v.frontPage w m i j k o:=fun hx=>h hx.1
    have hG o : ¬v.backPage w m i j k o:=fun hx=>h hx.1
    have hA:A=0:=OneQuill.one_sales_zero _ _ _ _ _ _ _ hF
    have hB:B=0:=OneQuill.one_sales_zero _ _ _ _ _ _ _ hG
    have hL:v.leftSales w m μ i j k=0:=OneQuill.one_good_sales_zero _ _ _ _ _ _ _ _ _ hF
    have hR:v.rightSales w m μ i j k=0:=OneQuill.one_good_sales_zero _ _ _ _ _ _ _ _ _ hG
    rw [hA,hB,hL,hR]
    simp only [Pi.zero_apply,le_refl,and_self,varOne,sub_self,abs_zero,Finset.sum_const_zero,
      forall_const,true_and]
    exact (bp_pos _).le

end OneStation
end
end Lax793645Proofs.Simplifications
