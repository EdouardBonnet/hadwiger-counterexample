import Lax793645Proofs.Simplifications.LinearPalette
import Lax793645Proofs.Simplifications.ExactPaintComparisons

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis Template Finset Matrix Function Filter
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {p : Shape} {q : Format} {d : Rates} {b : Bool} {b' : PreparationParameters} {s0 : ℕ}

def linearPaintCount (I : Type) [Fintype I] (R : ℕ) := Fintype.card (I→Vec (Fin R))
def linearPaletteSize (I : Type) [Fintype I] [DecidableEq I] (R : ℕ) :=
  paletteSize I (Fin (linearPaintCount I R))
def linearPaletteRank (I : Type) [Fintype I] (R : ℕ) :=
  Fintype.card (Fin (linearPaintCount I R)×I)*R

/-- Direct query comparison for a linear key test retains a bounded
linear unary palette. All bounds are chosen before the ambient dimension. -/
theorem linear_paint_side_release (w : Quill p q d b) (t : Tagging p (Messenger q))
    (z : Messenger q→F) (M : ℕ) (h : QueryParameters p M b' s0)
    (hw : w.moral t z) (R : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ u : ℝ,0<u ∧ ∀ᶠ n : ℕ in atTop,
      ∀ W : Wgt (Keys (p:=p) t (M*n)),(∀ x,|W x|≤1) →
      HasLinearCells (fun (_ : F) x=>W x) R →
      ∃ X : Silhouette p (M*n) (linearPaletteSize (Messenger q) R),
        LinearSilhouette X (linearPaletteRank (Messenger q) R) ∧
        w.markedTest t z M b' s0 n X W (bp (-(1/100:ℝ)*n)) u ε := by
  classical
  let K:=linearPaintCount (Messenger q) R
  let x:=2+num (Messenger q)
  let u:=ε/((K+1:ℝ)*x)
  have hx : 0<x:=by dsimp only [x,num]; positivity
  have hu : 0<u:=div_pos hε (mul_pos (by positivity) hx)
  have ht:=h.enter.first
  refine ⟨u,hu,?_⟩
  filter_upwards [w.resolve_ready t z M h hw u hu,litFire_calendar p b'.spJoint M h.thickness,
    eventually_ge_atTop (1:ℕ)] with n hn hfire hn1 W hW hlin
  obtain ⟨L,φ,hφ⟩:=linear_cells_exact hlin
  let ψ (y : Vec (Fin R)):=max (-1) (min 1 (φ 0 y))
  have hψ y : |ψ y|≤1 := abs_le.mpr
    ⟨le_max_left ..,max_le (by norm_num) (min_le_left ..)⟩
  have hψW (k : Keys (p:=p) t (M*n)) : ψ (L k)=W k := by
    have he:=hφ 0 k
    have hh:=abs_le.mp (hW k)
    dsimp only [ψ]
    rw [←he,min_eq_right hh.2,max_eq_right hh.1]
  have hK : Fintype.card (Messenger q→Vec (Fin R))=K := by
    simp [K,linearPaintCount,Vec]
  let E : (Messenger q→Vec (Fin R))≃Fin K:=Fintype.equivFinOfCardEq hK
  let f (i : Fin K):=linearPartitionPaint (w.pen t) L ψ (E.symm i)
  have hf i : |(f i).coeff|≤1:=hψ _
  have hflies i j : HasLinearCells
      (fun (_ : F) (k : AtomKey (p:=p) ((w.pen t).t j) (M*n))=>decide ((f i).flies j k)) R :=
    linear_partition_paint_coordinates (w.pen t) L ψ (E.symm i) j
  have hmural : mural (w.pen t) f=W := by
    have hh : mural (w.pen t) f=mural (w.pen t) (linearPartitionPaint (w.pen t) L ψ) := by
      funext k
      exact Equiv.sum_comp E.symm (fun a=>(linearPartitionPaint (w.pen t) L ψ a).cost k)
    rw [hh,linear_partition_mural]
    exact funext hψW
  obtain ⟨X,hXlin,hX⟩:=linear_build_palette (w.pen t) z f hflies
  refine ⟨X,hXlin,?_⟩
  rw [←hmural]
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
