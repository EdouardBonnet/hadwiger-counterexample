import Lax793645Proofs.Simplifications.AffinePredictedLabels
import Lax793645Proofs.Simplifications.PredictedPlans
import Lax793645Proofs.Simplifications.PredictorCells
import Lax793645Proofs.Simplifications.PredictedRareEvents

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis StatusAnalysis.DualAnalysis Matrix Function LinearMap
open scoped BigOperators
noncomputable section
variable {p : Shape} {n N M r s0 : ℕ} {A B : Rates} {b : PreparationParameters}

theorem affine_predicted_options_of_plan (P : PredictedPlan p A B r) (Γ : PredictionData p A B r)
    (Y : Silhouette p N r) (g : Bool → Augur p N)
    (hpulse : ∀ i, fromPulse Y (Γ.g i)=g i) (η : ℝ)
    (X : Charts p n A) (Z : Charts p n B) (T : Cross p n)
    (hP : P.good Γ (wisp p Y) η (hailing p X Z T))
    (s t : Pin p n N) (o v : UnitType p n N) (m : Mixer p n)
    (hj : 1 ≤ p.j) (hJ : 1 ≤ p.J) (hg : 3 ≤ p.g)
    (hlabels : b.B+2^(selectorProtectionDim p (affineQorth b.pins) b.pins+12) <
      Fintype.card (Label p.b))
    (hs : charted X s.sp) (ht : charted Z t.sp)
    (hK : planRank s.sp ≤ b.pins) (hK' : planRank t.sp ≤ b.pins)
    (hA : ∀ i, A i ≤ b.pins^2) (hB : ∀ i, B i ≤ b.pins^2)
    (hT : tableInj s.sp t.sp T) (hT' : tableInj t.sp s.sp (reciprocal p T))
    (hframe : PreparationParameters.frameSide p m o) (hframe' : PreparationParameters.frameSide p m v)
    (L R : Bool → Finset (Label p.b)) (hL : ∀ i, (L i).card ≤ b.B) (hR : ∀ i, (R i).card ≤ b.B)
    (ε : ℝ) (hclaim : claimed p o g m (fun i => X i (Γ.X i)) Γ.α L ε)
    (hclaim' : claimed p v g m (fun i => Z i (Γ.Y i)) Γ.α R ε) :
    ∃ (u : Quill p P.q A true) (w : Quill p P.q B false),
      let x : Typus p P.q A B := ⟨P.tag,P.diag,u,w⟩
      AffineOptions.chances x X Z s t T b.pins ∧
      u.baseSteady m b.pins X o ∧ w.baseSteady m b.pins Z v ∧
      u.predictionReady P.tag P.diag X m Γ.α g ε (tupleCell Y P.tag P.diag P.cell) o ∧
      w.predictionReady P.tag P.diag Z m Γ.α g ε (tupleCell Y P.tag P.diag P.cell) v := by
  classical
  obtain ⟨Pa⟩ := plan_protection_exists s.sp (affineQorth b.pins) b.pins hK
  obtain ⟨Pb⟩ := plan_protection_exists t.sp (affineQorth b.pins) b.pins hK' 
  have hcard := predicted_plan_card P Γ (wisp p Y) η (hailing p X Z T) hP
  obtain ⟨f,hf,hfresh,hLI⟩ := affine_predicted_labels Pa hj L hL hcard true hlabels
  obtain ⟨f',hf',hfresh',hLI'⟩ := affine_predicted_labels Pb hj R hR hcard false hlabels
  let F : Fabric p P.q A true := ⟨f,fun _ => Flavor.full,P.ampA⟩
  let G : Fabric p P.q B false := ⟨f',fun _ => Flavor.full,P.ampB⟩
  have hF : F.up P.tag P.diag :=
    ⟨hf,fun i => (hP.roleA i).2.1,fun i => (hP.roleA i).1⟩
  have hG : G.up P.tag P.diag :=
    ⟨hf',fun i => (hP.roleB i).2.1,fun i => (hP.roleB i).1⟩
  have hshort i : 1 ≤ P.q i ∧ P.q i ≤ 7 :=
    ⟨(hP.short i).1,(hP.short i).2.trans (by omega)⟩
  have hPa := Pa.protect_template ((F.hang 0).pen P.tag) hLI
  have hPb := Pb.protect_template ((G.hang 0).pen P.tag) hLI'
  obtain ⟨a,c,hopt⟩ := affine_optionVia P.q A B s t T b.pins hT hT' P.tag X Z hs ht F G
    hPa hPb P.diag hF hG hJ (by omega) hshort hP.solves
  refine ⟨F.hang a,G.hang c,hopt,?_,?_,?_,?_⟩
  · refine ⟨hframe,fun i => ⟨hA _,(hs _).2,fun y => ?_⟩,fun i => (hP.roleA i).2.2⟩
    refine (effective_rank (i:=parcel true i) ?_).trans hK
    rw [←(hs _).1]
    exact mem_range_self _ _
  · refine ⟨hframe',fun i => ⟨hB _,(ht _).2,fun y => ?_⟩,fun i => (hP.roleB i).2.2⟩
    refine (effective_rank (i:=parcel false i) ?_).trans hK'
    rw [←(ht _).1]
    exact mem_range_self _ _
  · refine ⟨Γ.X,L,hclaim,hfresh,?_⟩
    intro k hk i
    have he := congrArg (fun f : Augur p N => f (P.tag i) (P.diag i) (k i)) (hpulse (parcel true i))
    change Γ.g (parcel true i) (P.tag i) (P.diag i) (Y (P.tag i) (P.diag i) (k i))=_ at he
    rw [hk i] at he
    change (P.ampA i).2.2=_
    rw [hP.predictedA i,he]
    rfl
  · refine ⟨Γ.Y,R,hclaim',hfresh',?_⟩
    intro k hk i
    have he := congrArg (fun f : Augur p N => f (P.tag i) (P.diag i) (k i)) (hpulse (parcel false i))
    change Γ.g (parcel false i) (P.tag i) (P.diag i) (Y (P.tag i) (P.diag i) (k i))=_ at he
    rw [hk i] at he
    change (P.ampB i).2.2=_
    rw [hP.predictedB i,he]
    rfl

end
end Lax793645Proofs.Simplifications
