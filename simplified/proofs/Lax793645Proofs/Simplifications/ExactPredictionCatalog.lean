import Lax793645Proofs.Simplifications.ExactPredictionUniqueness
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.FinitePredictions

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis StatusAnalysis.DualAnalysis Function Finset
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
variable {p : Shape} {r : ℕ} {d : Rates}

def SamePrediction (u : Terrain p r) (f g : Pulsar p r) : Prop :=
  ∀ l q c,0<u l q c→f l q c=g l q c

def ExactCatalog (u : Terrain p r) (s : Gazette p r d)
    (B : ℕ) (f : Nodes→Pulsar p r) : Prop :=
  ∀ i E,(E.card≤B)→∀ w α g,
    ExactStatusPrediction u s i E (yokeSet w α) g→SamePrediction u g (f i)

/-- There is at most one canonical internal-bit predictor per endpoint.
The choice depends on the second unit alone, before sampling the first. -/
theorem exact_prediction_catalog {u : Terrain p r} {s : Gazette p r d} {β δ : ℝ}
    (hg : 3≤p.g) (hu : origami p r u δ) (hs : reports p r u s β δ) (hβ : 0<β)
    (B : ℕ) (hB : 2*B<Fintype.card (Label p.b))
    (Free : Pulsar p r→Prop) (hzero : Free 0)
    (hnorm : ∀ i E,E.card≤B→∀ w α f,
      ExactStatusPrediction u s i E (yokeSet w α) f→Free f) :
    ∃ f : Nodes→Pulsar p r,ExactCatalog u s B f ∧ ∀ i,Free (f i) := by
  classical
  have choice (i : Nodes) : ∃ f : Pulsar p r,Free f ∧
      ∀ E,E.card≤B→∀ w α g,
        ExactStatusPrediction u s i E (yokeSet w α) g→SamePrediction u g f := by
    by_cases h : ∃ E : Finset (Label p.b),∃ w α f,E.card≤B ∧
        ExactStatusPrediction u s i E (yokeSet w α) f
    · obtain ⟨E,w,α,f,hE,hf⟩:=h
      refine ⟨f,hnorm i E hE w α f hf,?_⟩
      intro E' hE' w' α' g hg'
      have hc : (E'∪E).card<Fintype.card (Label p.b) :=
        (card_union_le _ _).trans_lt (by omega)
      obtain ⟨_,_,he⟩:=exact_status_uniqueness hg hu hs hβ i (yokeSet w' α')
        (yokeSet w α) g f E' E hc hg' hf rfl
      intro l q c hc
      simpa only [yokeSet,zero_mul,add_zero] using he l q c hc
    refine ⟨0,hzero,?_⟩
    intro E hE w α g hg'
    exact (h ⟨E,w,α,g,hE,hg'⟩).elim
  choose f hf hcat using choice
  exact ⟨f,hcat,hf⟩

/-- Normalize the explicitly recorded tester coefficient by subtracting
it from the common predictor. In characteristic two this is a shift. -/
theorem exact_prediction_shift {u : Terrain p r} {s : Gazette p r d}
    (i : Nodes) (E : Finset (Label p.b)) (a : RhymeSet (d i)) (f : Pulsar p r)
    (ha : a.bit=1) (h : ExactStatusPrediction u s i E a f) :
    ExactStatusPrediction u s i E (yokeSet a.coal (1+a.headBit))
      (fun l q c=>f l q c+a.gamma*q) := by
  intro x hx hapt c hc v hv
  have hh:=h x hx hapt c hc v hv
  have he : a.soot x v=(yokeSet a.coal (1+a.headBit)).soot x v+a.gamma*x.q := by
    unfold RhymeSet.soot RhymeSet.read yokeSet
    rw [ha]
    simp only [zero_mul,add_zero,←add_assoc,char_two,zero_add]
  rw [he] at hh
  have hk:=congrArg (fun z : F=>z+a.gamma*x.q) hh
  simpa only [add_assoc,char_two,add_zero] using hk

end
end Lax793645Proofs.Simplifications
