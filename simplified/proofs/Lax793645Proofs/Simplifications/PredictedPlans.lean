import Lax793645Proofs.Simplifications.ShortPredictedLists
import Lax793645Proofs.Simplifications.RetainedPredictors

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis StatusAnalysis.DualAnalysis Matrix Function
open scoped BigOperators
noncomputable section
variable {p : Shape} {r : ℕ} {A B : Rates}

structure PredictedPlan (p : Shape) (A B : Rates) (r : ℕ) where
  q : Format
  tag : Tagging p (Messenger q)
  diag : Messenger q → F
  cell : Messenger q → Fin r
  ampA : Amounts p q A true
  ampB : Amounts p q B false

structure PredictedPlan.good (P : PredictedPlan p A B r) (v : PredictionData p A B r)
    (u : Terrain p r) (η : ℝ) (T : Cabinet A B) : Prop where
  short : ∀ i, 1 ≤ P.q i ∧ P.q i ≤ 3
  kept : ∀ i, η ≤ u (P.tag i) (P.diag i) (P.cell i)
  roleA : ∀ i, (P.ampA i).1.feasible (P.tag i) Flavor.full ∧
    (P.ampA i).1.sumBit=P.diag i ∧ (P.ampA i).1.diagO=(P.ampA i).2.1.1
  roleB : ∀ i, (P.ampB i).1.feasible (P.tag i) Flavor.full ∧
    (P.ampB i).1.sumBit=P.diag i ∧ (P.ampB i).1.diagO=(P.ampB i).2.1.1
  predictedA : ∀ i, (P.ampA i).2.2 = dotProduct (P.ampA i).2.1.2 (v.X (parcel true i)) +
    v.α (parcel true i)*(P.ampA i).2.1.1+v.g (parcel true i) (P.tag i) (P.diag i) (P.cell i)
  predictedB : ∀ i, (P.ampB i).2.2 = dotProduct (P.ampB i).2.1.2 (v.Y (parcel false i)) +
    v.α (parcel false i)*(P.ampB i).2.1.1+v.g (parcel false i) (P.tag i) (P.diag i) (P.cell i)
  solves : speak A B (sendSum P.diag P.ampA P.ampB)=(T,0)

theorem predicted_plan_exists (v : PredictionData p A B r) (u : Terrain p r) (η : ℝ)
    (T : Cabinet A B) (hT : ∀ i, (T i).1=1) (hg : 3 ≤ p.g)
    (hsolve : scorecard (fun i => predictedSpan (v.α i.1) (v.α i.2) (v.X i.1) (v.Y i.2)
      (retainedPatterns u v.g η i)) T) :
    ∃ P : PredictedPlan p A B r, P.good v u η T := by
  classical
  obtain ⟨s,hs,hsol⟩ := hsolve
  have hfirst i : (s i).1=1 := by
    rw [speak_val] at hsol
    have hh := congrArg (fun C : Court A B => (C.1 i).1) hsol
    exact hh.trans (hT i)
  choose q rr aa bb hlo hhi hmem hsum using fun i : Grid =>
    predicted_three_list (v.α i.1) (v.α i.2) (v.X i.1) (v.Y i.2)
      (retainedPatterns u v.g η i) (s i) (hs i) (hfirst i)
  choose tag cell hkept hleft hright using fun i : Grid => fun j : Fin (q i) => hmem i j
  choose roleA hfa hqa hda using fun i : Messenger q =>
    generic_summary p hg (tag i.1 i.2) (rr i.1 i.2).1 (aa i.1 i.2).1
  choose roleB hfb hqb hdb using fun i : Messenger q =>
    generic_summary p hg (tag i.1 i.2) (rr i.1 i.2).1 (bb i.1 i.2).1
  let PA : Amounts p q A true := fun i =>
    (roleA i,aa i.1 i.2,dotProduct (v.X i.1.1) (aa i.1 i.2).2+
      v.α i.1.1*(aa i.1 i.2).1+(rr i.1 i.2).2.1)
  let PB : Amounts p q B false := fun i =>
    (roleB i,bb i.1 i.2,dotProduct (v.Y i.1.2) (bb i.1 i.2).2+
      v.α i.1.2*(bb i.1 i.2).1+(rr i.1 i.2).2.2)
  let P : PredictedPlan p A B r :=
    ⟨q,fun i => tag i.1 i.2,fun i => (rr i.1 i.2).1,fun i => cell i.1 i.2,PA,PB⟩
  refine ⟨P,⟨fun i => ⟨hlo i,hhi i⟩,fun i => hkept i.1 i.2,
    fun i => ⟨hfa i,hqa i,hda i⟩,fun i => ⟨hfb i,hqb i,hdb i⟩,?_,?_,?_⟩⟩
  · intro i
    change dotProduct _ _+_+(rr i.1 i.2).2.1=_
    rw [hleft]
    rw [dotProduct_comm]
    rfl
  · intro i
    change dotProduct _ _+_+(rr i.1 i.2).2.2=_
    rw [hright]
    rw [dotProduct_comm]
    rfl
  · have he : sendSum P.diag P.ampA P.ampB=s := by
      funext i
      exact hsum i
    rw [he]
    exact hsol

theorem predicted_plan_card (P : PredictedPlan p A B r) (v : PredictionData p A B r)
    (u : Terrain p r) (η : ℝ) (T : Cabinet A B) (h : P.good v u η T) :
    Fintype.card (Messenger P.q) ≤ 12 := by
  rw [Fintype.card_sigma]
  have hh := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => (h.short i).2)
  simpa using hh

end
end Lax793645Proofs.Simplifications
