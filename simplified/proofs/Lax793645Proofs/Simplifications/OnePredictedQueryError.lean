import Lax793645Proofs.Simplifications.OneBaseQueries
import Lax793645Proofs.Simplifications.OneCommonPredictions

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis Filter Finset Matrix Function Template
open scoped BigOperators Topology Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OneQuill
variable {p:Shape} {q:Format} {d:Rates} {b:Bool} {n N:ℕ}
variable (w:Quill p q d b) (t:Tagging p (Messenger q)) (z:Messenger q→F)

def onePredictionHolds (m : Mixer p n) (o : OneUnit p n N)
    (marks : Bool → Profile p n) (α : Party) (g : Bool → OneAugur p N)
    (i : Messenger q) (y : Knobs p.g n) : Prop :=
  dialed p (t i) (w.flav i) y = z i ∧
    oneYoke m o (parcel b i) (marks (parcel b i)) (α (parcel b i))
      (useAtom p (t i) (w.sel i) (w.flav i) y) =
    g (parcel b i) (t i) (z i)
      (oneAtomKeyValue (o (parcel b i)) (t i) (w.sel i) (lit (w.flav i) (t i) y))

theorem one_prediction_failure_bound (m : Mixer p n) (o : OneUnit p n N)
    (marks : Bool → Profile p n) (α : Party) (g : Bool → OneAugur p N)
    (L : Bool → Finset (Label p.b)) {ε : ℝ}
    (hclaim : oneClaimed o g m marks α L ε) (hfresh : ∀ i, w.sel i ∉ L (parcel b i))
    (hw : w.moral t z) (hr : 1 ≤ p.r) (hn : 2*p.r ≤ n) (i : Messenger q) :
    pr ((w.pen t).state z n) (fun x => ¬onePredictionHolds w t z m o marks α g i (x i)) ≤
      (scanPrice p)⁻¹*ε := by
  classical
  let μ := w.policies t z n
  have hμ j : IsLaw (μ j) := Appearance.witLaw (w.allure_apt t z hw j) hr hn
  let P := onePredictionHolds w t z m o marks α g i
  have hmarg : pr ((w.pen t).state z n) (fun x => ¬P (x i)) = pr (μ i) (fun y => ¬P y) := by
    change pr (prodW μ) (fun x => ¬P (x i)) = pr (μ i) (fun y => ¬P y)
    have h := prodW_pr_inj (e:=fun _ : Unit => i) (by intro a b _; cases a; cases b; rfl)
      hμ (fun _ : Unit => fun y => ¬P y)
    simpa only [forall_const, Fintype.prod_unique] using h
  rw [hmarg]
  let Q := oneMismatch (g (parcel b i))
    (oneYoke m o (parcel b i) (marks (parcel b i)) (α (parcel b i)))
    (t i) (w.sel i) (w.flav i) (o (parcel b i))
  have hcar : carried (μ i) (fun y => dialed p (t i) (w.flav i) y=z i) :=
    normW_carried (subW_carried (spins p n) _)
  have hsub y (hy : μ i y ≠ 0) (hp : ¬P y) : Q y := by
    have hz : dialed p (t i) (w.flav i) y=z i := not_not.mp fun h => hy (hcar y h)
    intro he
    apply hp
    exact ⟨hz, by simpa only [hz] using he⟩
  have hcap y : μ i y ≤ (scanPrice p)⁻¹ * spins p n y :=
    on_mon (spins_law p n).nz (scanPrice_pos p)
      (dial_fraction p n _ _ _ hr hn (w.canDraw t z hw i)) y
  have hscale : pr (fun y => (scanPrice p)⁻¹*spins p n y) Q =
      (scanPrice p)⁻¹*pr (spins p n) Q := by
    unfold pr avg
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => mul_assoc _ _ _
  refine ((pr_on_mono (hμ i).nz hsub).trans (pr_mono_left hcap Q)).trans ?_
  rw [hscale]
  exact mul_le_mul_of_nonneg_left (hclaim _ _ (hfresh i) _ _) (inv_pos.mpr (scanPrice_pos p)).le

def OnePredictsOn (s : Charts p n d) (coords : ∀ j : Bool, Cell (d j))
    (α : Party) (g : Bool → OneAugur p N) (H : OneKeys t N → Prop) : Prop :=
  ∀ k, H k → ∀ i,
    (w.amp i).2.2 = dotProduct (w.amp i).2.1.2 (coords (parcel b i)) +
      α (parcel b i)*(w.amp i).2.1.1 + g (parcel b i) (t i) (z i) (k i)

theorem one_prediction_completes (s : Charts p n d) (m : Mixer p n) (o : OneUnit p n N)
    (coords : ∀ j : Bool, Cell (d j)) (α : Party) (g : Bool → OneAugur p N)
    (H : OneKeys t N → Prop) (hcell : OnePredictsOn w t z s coords α g H)
    (x : Inputs p n (Messenger q)) (hH : H (oneVolleyKeys ((w.pen t).draw x) t o))
    (hbase : oneBaseDeposit w t z m o s x)
    (hpred : ∀ i, onePredictionHolds w t z m o (fun j => s j (coords j)) α g i (x i)) :
    oneDeposit w t z m o s x := by
  refine ⟨funext fun i => ?_, hbase.2⟩
  have hi := hbase.1 i
  apply Prod.ext hi.1 (Prod.ext hi.2 ?_)
  let j := parcel b i
  let A := useAtom p (t i) (w.sel i) (w.flav i) (x i)
  have hrole : role p n A = (w.amp i).2.1.1 := congrArg Prod.fst hi.2
  have hbasis : roll (s j) (Tsym m A) = (w.amp i).2.1.2 := congrArg Prod.snd hi.2
  have hlinear : Tsym m (s j (coords j)) A =
      dotProduct (w.amp i).2.1.2 (coords j) := by
    rw [T_swap,roll_project,hbasis]
  have he := (hpred i).2
  change oneInner o j A + (Tsym m (s j (coords j)) A + α j * role p n A) = _ at he
  rw [hlinear,hrole] at he
  rw [hcell _ hH i]
  let v := dotProduct (w.amp i).2.1.2 (coords j)+α j*(w.amp i).2.1.1
  change oneInner o j A = v + _
  calc
    oneInner o j A = v+(oneInner o j A+v) := by
      rw [add_left_comm,char_two,add_zero]
    _ = _ := by rw [he]; rfl

set_option maxHeartbeats 1000000 in
theorem one_predicted_query_error (s : Charts p n d) (m : Mixer p n) (o : OneUnit p n N)
    (coords : ∀ j : Bool, Cell (d j)) (α : Party) (g : Bool → OneAugur p N)
    (L : Bool → Finset (Label p.b)) {ε : ℝ}
    (hclaim : oneClaimed o g m (fun j => s j (coords j)) α L ε)
    (hfresh : ∀ i, w.sel i ∉ L (parcel b i))
    (hw : w.moral t z) (hr : 1 ≤ p.r) (hn : 2*p.r ≤ n)
    (H : OneKeys t N → Prop) (hcell : OnePredictsOn w t z s coords α g H) :
    oneBaseProwl w t z s m o (fun k => ind (H k)) -
      Fintype.card (Messenger q)*((scanPrice p)⁻¹*ε) ≤
    oneProwl w t z o m s (fun k => ind (H k)) := by
  let μ := (w.pen t).state z n
  have hμ : IsLaw μ := by
    change IsLaw (prodW (w.policies t z n))
    exact prodW_law fun i => Appearance.witLaw (w.allure_apt t z hw i) hr hn
  have h := Lax793645Proofs.Simplifications.prediction_error_unnormalized μ hμ.nz
    (fun x => H (oneVolleyKeys ((w.pen t).draw x) t o)) (oneBaseDeposit w t z m o s)
    (oneDeposit w t z m o s)
    (fun i x => onePredictionHolds w t z m o (fun j => s j (coords j)) α g i (x i))
    (fun x hx hb hp => one_prediction_completes w t z s m o coords α g H hcell x hx hb hp)
    ((scanPrice p)⁻¹*ε)
    (fun i => one_prediction_failure_bound w t z m o _ α g L hclaim hfresh hw hr hn i)
  simpa only [μ,pr,oneDeposit,ind_and,mul_comm,mul_left_comm,mul_assoc,oneBaseProwl,oneProwl] using h

end OneQuill
end
end Lax793645Proofs.Simplifications
