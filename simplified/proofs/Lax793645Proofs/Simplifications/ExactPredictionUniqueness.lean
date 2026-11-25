import Lax793645Proofs.Simplifications.ExactStatusPredictions
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.UniqueStatusCoefficients

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis StatusAnalysis.DualAnalysis Function Finset
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {r : ℕ} {d : Rates}
variable {u : Terrain p r} {s : Gazette p r d} {β δ : ℝ}

/-- Exact predictions with the same internal-bit coefficient have the
same role and basis coefficients. Their functions differ only by the
explicit tester slope, on every positive reference cell. -/
theorem exact_status_uniqueness (hg : 3≤p.g) (hu : origami p r u δ)
    (hs : reports p r u s β δ) (hβ : 0<β) (i : Nodes)
    (a b : RhymeSet (d i)) (f g : Pulsar p r)
    (A B : Finset (Label p.b)) (hlabels : (A∪B).card<Fintype.card (Label p.b))
    (ha : ExactStatusPrediction u s i A a f)
    (hb : ExactStatusPrediction u s i B b g) (hbit : a.bit=b.bit) :
    a.coal=b.coal ∧ a.headBit=b.headBit ∧
      ∀ l q c,0<u l q c→f l q c+a.gamma*q=g l q c+b.gamma*q := by
  have hp:=unison hg hu hs i a b f g A B hlabels
    (exact_status_prediction_zero hu.1 hs.law i A a f ha)
    (exact_status_prediction_zero hu.1 hs.law i B b g hb) hbit
    (by linarith only [hβ] : (0:ℝ)+0<1/2*β) hβ.le
  refine ⟨hp.1,hp.2.1,?_⟩
  intro l q c hc
  by_contra hne
  have hh:=pr_mono (hu.1 l q).nz (p:=fun k=>k=c)
    (q:=fun k=>f l q k+a.gamma*q≠g l q k+b.gamma*q)
    (fun k hk=>hk.symm ▸ hne)
  rw [pr_point'] at hh
  have hb:=hp.2.2 l q
  linarith only [hc,hh,hb]

/-- A prediction with no internal bit is the displayed tester term
alone. Positivity of the role and basis assignments rules out all other
coefficients. -/
theorem exact_zero_bit_prediction (hg : 3≤p.g) (hu : origami p r u δ)
    (hs : reports p r u s β δ) (hβ : 0<β) (i : Nodes)
    (a : RhymeSet (d i)) (f : Pulsar p r) (A : Finset (Label p.b))
    (hlabels : A.card<Fintype.card (Label p.b))
    (ha : ExactStatusPrediction u s i A a f) (hbit : a.bit=0) :
    a.coal=0 ∧ a.headBit=0 ∧ ∀ l q c,0<u l q c→f l q c=a.gamma*q := by
  let z : RhymeSet (d i):=⟨0,0,0,0⟩
  have hz : ExactStatusPrediction u s i ∅ z 0 := by
    intro x hx hapt c hc v hv
    simp [RhymeSet.soot,RhymeSet.read,z]
  have hAB : (A∪∅).card<Fintype.card (Label p.b):=by simpa using hlabels
  obtain ⟨hc,hh,hf⟩:=exact_status_uniqueness hg hu hs hβ i a z f 0 A ∅ hAB ha hz hbit
  refine ⟨hc,hh,?_⟩
  intro l q c hpos
  have he:=hf l q c hpos
  change f l q c+a.gamma*q=0+0*q at he
  have hsum : f l q c+a.gamma*q=0:=by simpa only [zero_mul,add_zero] using he
  have h:=congrArg (fun v : F=>v+a.gamma*q) hsum
  simpa only [add_assoc,char_two,add_zero,zero_add] using h

end
end Lax793645Proofs.Simplifications
