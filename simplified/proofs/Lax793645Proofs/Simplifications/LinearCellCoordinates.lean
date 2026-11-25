import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.CommonPredictions

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Function Finset
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {V Q A B T : Type} [AddCommGroup V] [Module F V]

/-- One set of linear coordinates works for every status of the prefix
(in particular, both possible diagonal bits). -/
def HasLinearCells (f : Q→V→A) (R : ℕ) : Prop :=
  ∃ r : ℕ,r≤R ∧ ∃ L : V→ₗ[F] Vec (Fin r),∃ φ : Q→Vec (Fin r)→A,
    ∀ q x,f q x=φ q (L x)

theorem linear_cells_mono {f : Q→V→A} {R S : ℕ}
    (h : HasLinearCells f R) (hRS : R≤S) : HasLinearCells f S := by
  obtain ⟨r,hr,L,φ,hφ⟩:=h
  exact ⟨r,hr.trans hRS,L,φ,hφ⟩

theorem linear_cells_postprocess {f : Q→V→A} {R : ℕ}
    (h : HasLinearCells f R) (ψ : Q→A→B) :
    HasLinearCells (fun q x=>ψ q (f q x)) R := by
  obtain ⟨r,hr,L,φ,hφ⟩:=h
  exact ⟨r,hr,L,fun q y=>ψ q (φ q y),fun q x=>congrArg (ψ q) (hφ q x)⟩

theorem linear_cells_precompose {W : Type} [AddCommGroup W] [Module F W]
    {f : Q→V→A} {R : ℕ} (h : HasLinearCells f R) (P : W→ₗ[F]V) :
    HasLinearCells (fun q x=>f q (P x)) R := by
  obtain ⟨r,hr,L,φ,hφ⟩:=h
  exact ⟨r,hr,L.comp P,φ,fun q x=>hφ q (P x)⟩

theorem linear_cells_constant (f : Q→A) : HasLinearCells (fun q (_ : V)=>f q) 0 :=
  ⟨0,le_rfl,0,fun q _=>f q,fun _ _=>rfl⟩

/-- Pad the coordinate list with zero rows. This keeps both the palette
size and its coordinate budget fixed before the dimension tends to infinity. -/
theorem linear_cells_exact {f : Q→V→A} {R : ℕ} (h : HasLinearCells f R) :
    ∃ L : V→ₗ[F] Vec (Fin R),∃ φ : Q→Vec (Fin R)→A,
      ∀ q x,f q x=φ q (L x) := by
  classical
  obtain ⟨r,hr,L,φ,hφ⟩:=h
  let P : V→ₗ[F] Vec (Fin R) :=
    { toFun:=fun x i=>if hi:i.val<r then L x ⟨i.val,hi⟩ else 0
      map_add':=fun x y=>by
        ext i
        split_ifs with hi <;> simp [hi,map_add]
      map_smul':=fun c x=>by
        ext i
        split_ifs with hi <;> simp [hi,map_smul] }
  refine ⟨P,fun q y=>φ q (fun i=>y (Fin.castLE hr i)),?_⟩
  intro q x
  rw [hφ q x]
  congr 1
  funext i
  change L x i=(if hi:i.val<r then L x ⟨i.val,hi⟩ else 0)
  rw [dif_pos i.isLt]

/-- Bundling finitely many coordinate certificates adds their dimensions.
This is the same bundling used by the actual common predictor dictionary. -/
theorem linear_cells_bundle [Fintype T] {B : T→Type} (R : T→ℕ)
    (f : ∀ t,Q→V→B t) (h : ∀ t,HasLinearCells (f t) (R t)) :
    HasLinearCells (fun q x t=>f t q x) (∑ t,R t) := by
  classical
  choose r hr L φ hφ using h
  let D:=Σ t,Fin (r t)
  let e:=Fintype.equivFin D
  let P : V→ₗ[F] Vec (Fin (Fintype.card D)) :=
    { toFun:=fun x j=>L (e.symm j).1 x (e.symm j).2
      map_add':=fun x y=>by ext j; simp only [map_add,Pi.add_apply]
      map_smul':=fun a x=>by ext j; simp only [map_smul,Pi.smul_apply,RingHom.id_apply] }
  have hsize : Fintype.card D≤∑ t,R t := by
    simp only [D,Fintype.card_sigma,Fintype.card_fin]
    exact Finset.sum_le_sum fun t _=>hr t
  refine ⟨Fintype.card D,hsize,P,fun q x t=>φ t q (fun j=>x (e ⟨t,j⟩)),?_⟩
  intro q x
  funext t
  change f t q x=φ t q (fun j=>(P x) (e ⟨t,j⟩))
  rw [hφ t q x]
  congr 1
  funext j
  change L t x j=L (e.symm (e ⟨t,j⟩)).1 x (e.symm (e ⟨t,j⟩)).2
  rw [Equiv.symm_apply_apply]

variable {p : Shape} {N : ℕ}

def LinearAugur (g : Augur p N) (K : ℕ) :=
  ∀ l,HasLinearCells (g l) K

end
end Lax793645Proofs.Simplifications
