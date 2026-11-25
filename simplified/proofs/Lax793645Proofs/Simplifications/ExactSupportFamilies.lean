import Lax793645Proofs.Simplifications.ExactSupportPredictions
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.BinaryStatusComparison

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis StatusAnalysis.DualAnalysis Function
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- One possible status can be chosen from any finite probability law. -/
theorem law_support_nonempty {A : Type} [Fintype A] (w : Wgt A) (hw : IsLaw w) :
    ∃ a,0<w a := by
  obtain ⟨a,_,ha⟩:=exists_of_pr_pos hw.nz
    (show 0<pr w (fun _=>True) by rw [pr_true,hw.total]; norm_num)
  exact ⟨a,ha⟩

/-- Relations between every pair of possible statuses give a common
predictor for whole families of labels. The construction chooses one
possible value; no majority vote or error estimate is used. -/
theorem exact_family_predictor {I J C A B : Type}
    [Nonempty I] [Nonempty J] [Fintype A] [Fintype B]
    (w : I→C→Wgt A) (v : J→C→Wgt B)
    (hw : ∀ i c,IsLaw (w i c)) (hv : ∀ j c,IsLaw (v j c))
    (a : I→A→F) (b : J→B→F) (P : C→Prop)
    (h : ∀ c,P c→∀ i j x y,0<w i c x→0<v j c y→a i x=b j y) :
    ∃ φ : C→F,
      (∀ c,P c→∀ i x,0<w i c x→a i x=φ c) ∧
      (∀ c,P c→∀ j y,0<v j c y→b j y=φ c) := by
  classical
  let S (c : {c:C // P c}) : Set (I×A):={x | 0<w x.1 c.val x.2}
  let T (c : {c:C // P c}) : Set (J×B):={x | 0<v x.1 c.val x.2}
  have hS (c : {c:C // P c}) : (S c).Nonempty := by
    let i:I:=Classical.choice inferInstance
    obtain ⟨x,hx⟩:=law_support_nonempty (w i c.val) (hw i c.val)
    exact ⟨(i,x),hx⟩
  have hT (c : {c:C // P c}) : (T c).Nonempty := by
    let j:J:=Classical.choice inferInstance
    obtain ⟨y,hy⟩:=law_support_nonempty (v j c.val) (hv j c.val)
    exact ⟨(j,y),hy⟩
  have hrel (c : {c:C // P c}) (x : I×A) (hx : x∈S c)
      (y : J×B) (hy : y∈T c) : a x.1 x.2+b y.1 y.2=0 := by
    rw [h c.val c.property x.1 y.1 x.2 y.2 hx hy,char_two]
  obtain ⟨ψ,hψ,hψ'⟩:=support_rectangle_constant S T
    (fun x=>a x.1 x.2) (fun y=>b y.1 y.2) (fun _=>0) hS hT hrel
  let φ (c : C):=if hc:P c then ψ ⟨c,hc⟩ else 0
  refine ⟨φ,?_,?_⟩
  · intro c hc i x hx
    exact (hψ ⟨c,hc⟩ (i,x) hx).trans (by simp only [φ,dif_pos hc])
  · intro c hc j y hy
    simpa only [φ,dif_pos hc,add_zero] using hψ' ⟨c,hc⟩ (j,y) hy

end
end Lax793645Proofs.Simplifications
