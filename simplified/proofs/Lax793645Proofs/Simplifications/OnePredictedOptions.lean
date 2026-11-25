import Lax793645Proofs.Simplifications.OnePredictedLabels
import Lax793645Proofs.Simplifications.PredictedPlans
import Lax793645Proofs.Simplifications.OnePredictorCells
import Lax793645Proofs.Simplifications.OnePredictedRareEvents

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis StatusAnalysis.DualAnalysis Matrix Function LinearMap
open scoped BigOperators Classical
set_option backward.isDefEq.respectTransparency false
noncomputable section
variable {p : Shape} {n N M r s0 : ℕ} {A B : Rates} {b : PreparationParameters}

theorem one_predicted_options_of_plan (P : PredictedPlan p A B r) (Γ : PredictionData p A B r)
    (Y : OneSilhouette p N r) (g : Bool → OneAugur p N)
    (hpulse : ∀ i, oneFromPulse Y (Γ.g i)=g i) (η : ℝ)
    (X : Charts p n A) (Z : Charts p n B) (T : OneCross p n)
    (hP : P.good Γ (oneWisp p Y) η (oneHailing X Z T))
    (s t : ImagePin (Comp p.g) (OneColumn p n) (2*N)) (o v : OneUnit p n N) (m : Mixer p n)
    (hj : 1 ≤ p.j) (hJ : 1 ≤ p.J) (hg : 3 ≤ p.g) (hodd : Odd p.g)
    (hlabels : b.B+2^(oneSelectorProtectionDim p (onePreparationPins b)+12) <
      Fintype.card (Label p.b))
    (hs : oneCharted X s.sp) (ht : oneCharted Z t.sp)
    (hK : imagePlanRank s.sp ≤ (onePreparationPins b)) (hK' : imagePlanRank t.sp ≤ (onePreparationPins b))
    (hA : ∀ i, A i ≤ (onePreparationPins b)^2) (hB : ∀ i, B i ≤ (onePreparationPins b)^2)
    (hT : oneTableSafe s.sp t.sp T) (hT' : oneTableSafe t.sp s.sp (fun e=>(T e)ᵀ))
    (hframe : oneFrameSide m o) (hframe' : oneFrameSide m v)
    (L R : Bool → Finset (Label p.b)) (hL : ∀ i, (L i).card ≤ b.B) (hR : ∀ i, (R i).card ≤ b.B)
    (ε : ℝ) (hclaim : oneClaimed o g m (fun i => X i (Γ.X i)) Γ.α L ε)
    (hclaim' : oneClaimed v g m (fun i => Z i (Γ.Y i)) Γ.α R ε) :
    ∃ (u : Quill p P.q A true) (w : Quill p P.q B false),
      let x : Typus p P.q A B := ⟨P.tag,P.diag,u,w⟩
      OneOptions.chances x X Z s t T (onePreparationPins b) ∧
      OneQuill.OneBaseSteady u m (onePreparationPins b) X o ∧ OneQuill.OneBaseSteady w m (onePreparationPins b) Z v ∧
      OneQuill.OnePredictionReady u P.tag P.diag X m Γ.α g ε (oneTupleCell Y P.tag P.diag P.cell) o ∧
      OneQuill.OnePredictionReady w P.tag P.diag Z m Γ.α g ε (oneTupleCell Y P.tag P.diag P.cell) v := by
  classical
  obtain ⟨Pa⟩ := one_plan_protection_exists s.sp (onePreparationPins b) (fun e=>(image_plan_component_dimension _ e).trans hK)
  obtain ⟨Pb⟩ := one_plan_protection_exists t.sp (onePreparationPins b) (fun e=>(image_plan_component_dimension _ e).trans hK') 
  have hcard := predicted_plan_card P Γ (oneWisp p Y) η (oneHailing X Z T) hP
  obtain ⟨f,hf,hfresh,hLI⟩ := one_predicted_labels Pa hj L hL hcard true hlabels
  obtain ⟨f',hf',hfresh',hLI'⟩ := one_predicted_labels Pb hj R hR hcard false hlabels
  let F : Fabric p P.q A true := ⟨f,fun _ => Flavor.full,P.ampA⟩
  let G : Fabric p P.q B false := ⟨f',fun _ => Flavor.full,P.ampB⟩
  have hF : F.up P.tag P.diag :=
    ⟨hf,fun i => (hP.roleA i).2.1,fun i => (hP.roleA i).1⟩
  have hG : G.up P.tag P.diag :=
    ⟨hf',fun i => (hP.roleB i).2.1,fun i => (hP.roleB i).1⟩
  have hshort i : 1 ≤ P.q i ∧ P.q i ≤ 7 :=
    ⟨(hP.short i).1,(hP.short i).2.trans (by omega)⟩
  have hPa := Pa.protect_template ((F.hang 0).pen P.tag) (hcard.trans (by omega)) hLI
  have hPb := Pb.protect_template ((G.hang 0).pen P.tag) (hcard.trans (by omega)) hLI'
  obtain ⟨a,c,hopt⟩ := OneOptions.optionVia P.q A B s t T (onePreparationPins b) hT hT' P.tag X Z hs ht F G
    hPa hPb P.diag hF hG hJ hg hodd hshort hP.solves
  refine ⟨F.hang a,G.hang c,hopt,?_,?_,?_,?_⟩
  · refine ⟨hframe,fun i => ⟨hA _,(hs _).2,fun y => ?_⟩,fun i => (hP.roleA i).2.2,fun _=>rfl⟩
    refine (one_effective_rank s.sp (parcel true i) _ ?_).trans hK
    rw [←(hs _).1]
    exact mem_range_self _ _
  · refine ⟨hframe',fun i => ⟨hB _,(ht _).2,fun y => ?_⟩,fun i => (hP.roleB i).2.2,fun _=>rfl⟩
    refine (one_effective_rank t.sp (parcel false i) _ ?_).trans hK'
    rw [←(ht _).1]
    exact mem_range_self _ _
  · refine ⟨Γ.X,L,hclaim,hfresh,?_⟩
    intro k hk i
    have he := congrArg (fun f : OneAugur p N => f (P.tag i) (P.diag i) (k i)) (hpulse (parcel true i))
    change Γ.g (parcel true i) (P.tag i) (P.diag i) (Y (P.tag i) (P.diag i) (k i))=_ at he
    rw [hk i] at he
    change (P.ampA i).2.2=_
    rw [hP.predictedA i,he]
    rfl
  · refine ⟨Γ.Y,R,hclaim',hfresh',?_⟩
    intro k hk i
    have he := congrArg (fun f : OneAugur p N => f (P.tag i) (P.diag i) (k i)) (hpulse (parcel false i))
    change Γ.g (parcel false i) (P.tag i) (P.diag i) (Y (P.tag i) (P.diag i) (k i))=_ at he
    rw [hk i] at he
    change (P.ampB i).2.2=_
    rw [hP.predictedB i,he]
    rfl

end
end Lax793645Proofs.Simplifications
