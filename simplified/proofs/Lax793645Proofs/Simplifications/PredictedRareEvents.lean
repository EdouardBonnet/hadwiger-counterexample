import Lax793645Proofs.Simplifications.PredictedQueryError
import Lax793645Proofs.Simplifications.RestrictedSuperlevels
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.RareLeafEvents

namespace Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
noncomputable section
open Filter Finset Matrix Function
open scoped BigOperators Topology
open Template
namespace StatusAnalysis
variable {p : Shape} {q : Format} {d e : Rates} {b : Bool} {n N K : ℕ}

namespace Quill
variable (w : Quill p q d b) (t : Tagging p (Messenger q)) (z : Messenger q → F)

def predictionReady (s : Charts p n d) (m : Mixer p n)
    (α : Party) (g : Bool → Augur p N) (ε : ℝ)
    (E : Keys (p:=p) t N → Prop) (o : UnitType p n N) : Prop :=
  ∃ (coords : ∀ j : Bool, Cell (d j)) (L : Bool → Finset (Label p.b)),
    claimed p o g m (fun j => s j (coords j)) α L ε ∧
    (∀ i, w.sel i ∉ L (parcel b i)) ∧ w.predictsOn t z s coords α g E

def predictedQualified (s : Charts p n d) (m : Mixer p n) (K : ℕ)
    (μ : Wgt (UnitType p n N)) (P : UnitType p n N → Prop) (a : ℝ)
    (α : Party) (g : Bool → Augur p N) (ε : ℝ) (E : Keys (p:=p) t N → Prop) : Prop :=
  2*a ≤ pr μ P ∧ ∀ o, P o → μ o ≠ 0 →
    w.baseSteady m K s o ∧ w.predictionReady t z s m α g ε E o

theorem predicted_qualify_hit (s : Charts p n d) (m : Mixer p n) (K : ℕ)
    (μ : Wgt (UnitType p n N)) (P : UnitType p n N → Prop)
    (α : Party) (g : Bool → Augur p N) (ε : ℝ)
    (E H : Keys (p:=p) t N → Prop) (hHE : ∀ x, H x → E x)
    {a h : ℝ} (hh : 0 < h)
    (hq : w.predictedQualified t z s m K μ P a α g ε E)
    (hμ : IsLaw μ) (hw : w.moral t z) (hr : 1 ≤ p.r) (hn : 2*p.r ≤ n)
    (herr : Fintype.card (Messenger q)*((scanPrice p)⁻¹*ε) ≤ h)
    (hbad : pr μ (fun o => ¬w.baseSober t z K H m (2*h) o) ≤ a) :
    a*h ≤ pr (w.sales t z μ P m s) H := by
  classical
  let Q := w.baseSober t z K H m (2*h)
  let V o := w.prowl s t z m o (fun x => ind (H x))
  have he : a ≤ pr μ (fun x => P x ∧ Q x) :=
    le_trans (by linarith only [hbad,hq.1]) (pr_shield hμ.nz P Q)
  unfold pr
  rw [sales_mean]
  refine (mul_le_mul_of_nonneg_right he hh.le).trans ?_
  unfold pr
  rw [←avg_mul]
  unfold avg
  refine Finset.sum_le_sum fun o _ => ?_
  dsimp only
  by_cases ho : μ o=0
  · simp only [ho,zero_mul]; rfl
  apply mul_le_mul_of_nonneg_left _ (hμ.nz o)
  have hstate : IsLaw ((w.pen t).state z n) := by
    change IsLaw (prodW (w.policies t z n))
    exact prodW_law fun i => Appearance.witLaw (w.allure_apt t z hw i) hr hn
  have hV : 0 ≤ V o := avg_nonneg hstate.nz fun x => mul_nonneg (ind_nonneg _) (ind_nonneg _)
  by_cases hp : P o ∧ Q o
  · change ind (_∧_) * _ ≤ _*V o
    rw [ind_one hp,ind_one hp.1,one_mul,one_mul]
    obtain ⟨hb,coords,L,hclaim,hfresh,hcell⟩ := hq.2 o hp.1 ho
    have hbase := hp.2 s hb
    have hfull := w.predicted_query_error t z s m o coords α g L hclaim hfresh hw hr hn H
      (fun k hk => hcell k (hHE k hk))
    change _ ≤ V o at hfull
    linarith only [hbase,hfull,herr]
  rw [ind_zero hp,zero_mul]
  exact mul_nonneg (ind_nonneg _) hV

theorem sales_mono_filter (s : Charts p n d) (m : Mixer p n)
    (μ : Wgt (UnitType p n N)) (P Q : UnitType p n N → Prop)
    (hμ : ∀ x, 0 ≤ μ x) (hPQ : ∀ o, P o → Q o) :
    ∀ k, w.sales t z μ P m s k ≤ w.sales t z μ Q m s k := by
  intro k
  apply avg_mono (prodW_nonneg fun _ => normW_nonneg (subW_nonneg (spins_law ..).nz _))
  exact fun x => pr_mono hμ (fun o ho => ⟨⟨hPQ o ho.1.1,ho.1.2⟩,ho.2⟩)

end Quill

namespace Station
variable {s : LeafMixture p n N} (v : Station p n N K s) (x : Typus p q d e)
  (m : Mixer p n) (k : Fin (2^deckMax p K)) (μ : Wgt (UnitType p n N))

def predictedCharter (a : ℝ) (α : Party) (g : Bool → Augur p N) (ε : ℝ)
    (E : Keys (p:=p) x.t N → Prop) (i : s.T × s.T) : Prop :=
  x.permission ∧ ∃ (P Q : UnitType p n N → Prop),
    (∀ o, P o → v.frontPage x m i.1 i.2 k o) ∧
    (∀ o, Q o → v.backPage x m i.1 i.2 k o) ∧
    x.qA.predictedQualified x.t x.z (v.cAxes i.1 d) m K (partW μ i.1.val) P a α g ε E ∧
    x.qB.predictedQualified x.t x.z (v.cAxes i.2 e) m K (partW μ i.2.val) Q a α g ε E

def predictedBerth (a : ℝ) (α : Party) (g : Bool → Augur p N) (ε : ℝ)
    (E : Keys (p:=p) x.t N → Prop) : ℝ :=
  pr (pairW (portionW μ s.T) (portionW μ s.T))
    (v.predictedCharter x m k μ a α g ε E)

end Station
end StatusAnalysis

theorem overlap_mono_nonnegative {A : Type} [Fintype A] (ν f g F G : Wgt A)
    (hν : ∀ x, 0 ≤ ν x) (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hF : ∀ x, f x ≤ F x) (hG : ∀ x, g x ≤ G x) :
    overlap ν f g ≤ overlap ν F G := by
  apply avg_mono hν
  intro x
  exact mul_le_mul (div_le_div_of_nonneg_right (hF x) (hν x))
    (div_le_div_of_nonneg_right (hG x) (hν x)) (div_nonneg (hg x) (hν x))
    (div_nonneg ((hf x).trans (hF x)) (hν x))

end
end Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
