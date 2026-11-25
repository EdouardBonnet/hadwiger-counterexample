import Lax793645Proofs.Simplifications.LinearPredictorCertificates
import Lax793645Proofs.Simplifications.LinearPartitionPaints

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis Template Finset Matrix Function
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {N R : ℕ} {A B : Type}
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- Keep the linear certificate when the finite palette records all the
unary cell tests in an exact product decomposition. -/
theorem linear_build_palette (v : Template p A) (z : A→F)
    (w : B→Paint v N)
    (hlin : ∀ i j,HasLinearCells
      (fun (_ : F) (x : AtomKey (p:=p) (v.t j) N)=>decide ((w i).flies j x)) R) :
    ∃ Y : Silhouette p N (paletteSize A B),
      LinearSilhouette Y (Fintype.card (B×A)*R) ∧ ∀ i,pigments z Y (w i) := by
  classical
  let E:=Fintype.equivFin (B×A→Bool)
  let H (l : Tag p.g) (_ : F) (x : AtomKey (p:=p) l N) (i : B×A) :=
    if h:v.t i.2=l then decide ((w i.1).flies i.2 (h ▸ x)) else false
  let Y : Silhouette p N (paletteSize A B):=fun l q x=>E (H l q x)
  refine ⟨Y,?_,?_⟩
  · intro l
    have hi (i : B×A) : HasLinearCells (fun q x=>H l q x i) R := by
      by_cases h : v.t i.2=l
      · subst l
        simpa only [H,dif_pos rfl] using hlin i.1 i.2
      · have hc:=linear_cells_constant (V:=AtomKey (p:=p) l N) (fun _ : F=>false)
        have hm:=linear_cells_mono hc (Nat.zero_le R)
        simpa only [H,dif_neg h] using hm
    have hh:=linear_cells_postprocess
      (linear_cells_bundle (fun _ : B×A=>R) (fun i q x=>H l q x i) hi)
      (fun (_ : F) x=>E x)
    simpa only [Finset.sum_const,Finset.card_univ,smul_eq_mul] using hh
  · intro i j
    refine ⟨fun x=>E.symm x (i,j),?_⟩
    intro x
    change (w i).flies j x ↔ E.symm (E (H (v.t j) (z j) x)) (i,j)=true
    rw [Equiv.symm_apply_apply]
    simp only [H,dif_pos rfl,decide_eq_true_eq]

/-- Each unary factor of the exact linear-cell product identity has the
same bounded linear-coordinate certificate. -/
theorem linear_partition_paint_coordinates (v : Template p A)
    (L : Keys (p:=p) v.t N→ₗ[F] Vec (Fin R)) (φ : Wgt (Vec (Fin R)))
    (a : A→Vec (Fin R)) (j : A) :
    HasLinearCells (fun (_ : F) (x : AtomKey (p:=p) (v.t j) N)=>
      decide ((linearPartitionPaint v L φ a).flies j x)) R := by
  classical
  let S : AtomKey (p:=p) (v.t j) N→ₗ[F] Keys (p:=p) v.t N :=
    { toFun:=fun x=>(Pi.single j x : Keys (p:=p) v.t N)
      map_add':=fun x y=>Pi.single_add (f:=fun i=>AtomKey (p:=p) (v.t i) N) j x y
      map_smul':=fun c x=>Pi.single_smul (f:=fun i=>AtomKey (p:=p) (v.t i) N) j c x }
  refine ⟨R,le_rfl,L.comp S,fun _ y=>decide (y=a j),?_⟩
  intro q x
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  rfl

/-- A concrete common linear query partition produces a linear unary
palette, rather than merely an arbitrary finite palette. -/
theorem linear_partition_palette (v : Template p A) (z : A→F)
    (L : Keys (p:=p) v.t N→ₗ[F] Vec (Fin R)) (φ : Wgt (Vec (Fin R))) :
    ∃ Y : Silhouette p N (paletteSize A (A→Vec (Fin R))),
      LinearSilhouette Y (Fintype.card ((A→Vec (Fin R))×A)*R) ∧
      ∀ a,pigments z Y (linearPartitionPaint v L φ a) :=
  linear_build_palette v z (linearPartitionPaint v L φ)
    (fun a j=>linear_partition_paint_coordinates v L φ a j)

end
end Lax793645Proofs.Simplifications
