import Lax793645Proofs.Simplifications.LinearPartitionPaints
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.UniformSideComparisons

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis Template Finset Matrix Function Filter
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
variable {p : Shape} {q : Format} {d : Rates} {b : Bool} {b' : PreparationParameters} {s0 : ℕ}

/-- Exact finite product tests use only binary mixing and unary cell
comparison. No weak-product approximation is needed for this interface. -/
theorem exact_paint_side_release (w : Quill p q d b) (t : Tagging p (Messenger q))
    (z : Messenger q→F) (M : ℕ) (h : QueryParameters p M b' s0)
    (hw : w.moral t z) (K : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ u : ℝ,0<u ∧ ∀ᶠ n : ℕ in atTop,
      ∀ W : Wgt (Keys (p:=p) t (M*n)),design (w.pen t) W 1 K →
      ∃ X : Silhouette p (M*n) (paletteSize (Messenger q) (Fin K)),
        w.markedTest t z M b' s0 n X W (bp (-(1/100:ℝ)*n)) u ε := by
  let x:=2+num (Messenger q)
  let u:=ε/((K+1:ℝ)*x)
  have hx : 0<x:=by dsimp only [x,num]; positivity
  have hu : 0<u:=div_pos hε (mul_pos (by positivity) hx)
  have ht:=h.enter.first
  refine ⟨u,hu,?_⟩
  filter_upwards [w.resolve_ready t z M h hw u hu,litFire_calendar p b'.spJoint M h.thickness,
    eventually_ge_atTop (1:ℕ)] with n hn hfire hn1 W hdesign
  obtain ⟨f,rfl,hf⟩:=hdesign
  obtain ⟨X,hX⟩:=buildPalette (w.pen t) (M*n) z f
  refine ⟨X,?_⟩
  intro r Y hY m U hm
  have hsubset : ∀ o,w.flunk t z Y (mural (w.pen t) f) m u ε o → ¬litFire p o := by
    intro o ho hlit
    obtain ⟨hframe,harea,s,hbad⟩:=ho
    have hready:=hn m hm.cols hm.rum r Y o hframe harea hlit
    have hpig i:=finerPigment X Y hY (f i) (hX i)
    have hh:=w.paint_set t z m Y o s f hpig (by linarith only [ht.hG]) ht.hJ hf hready
    have heq : (K+1:ℝ)*(x*u)=ε := by dsimp only [u]; field_simp
    have hcost : (K:ℝ)*(x*u)≤ε := by
      rw [←heq]
      exact mul_le_mul_of_nonneg_right (by linarith) (mul_pos hx hu).le
    exact (not_lt_of_ge (hh.trans hcost)) hbad
  have he:=((pr_mono hm.drain.1.nz hsubset).trans (hfire m hm.cols U hm.drain.2.2.2))
  refine he.trans (bp_le ?_)
  have hn : (1:ℝ)≤n:=by exact_mod_cast hn1
  nlinarith only [hn]

end
end Lax793645Proofs.Simplifications
