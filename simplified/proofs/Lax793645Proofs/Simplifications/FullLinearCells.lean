import Lax793645Proofs.Simplifications.LinearCellCoordinates

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Function LinearMap Module Finset
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {V Q A B T : Type} [AddCommGroup V] [Module F V]

/-- The cells are precisely the fibers of one linear map. Merely being
a function of linear coordinates would permit arbitrary coarsenings. -/
def HasFullLinearCells (f : Q→V→A) (R : ℕ) : Prop :=
  ∃ r : ℕ,r≤R ∧ ∃ L : V→ₗ[F]Vec (Fin r),
    ∀ q x y,f q x=f q y ↔ L x=L y

theorem HasFullLinearCells.hasLinearCells {f : Q→V→A} {R : ℕ}
    (h : HasFullLinearCells f R) : HasLinearCells f R := by
  classical
  obtain ⟨r,hr,L,hL⟩:=h
  let φ (q : Q) (z : Vec (Fin r)):=
    if hz : ∃ x,L x=z then f q hz.choose else f q 0
  refine ⟨r,hr,L,φ,fun q x=>?_⟩
  dsimp only [φ]
  rw [dif_pos (show ∃ y,L y=L x from ⟨x,rfl⟩)]
  exact (hL q _ _).mpr (Exists.choose_spec (show ∃ y,L y=L x from ⟨x,rfl⟩)).symm

theorem full_linear_cells_mono {f : Q→V→A} {R S : ℕ}
    (h : HasFullLinearCells f R) (hRS : R≤S) : HasFullLinearCells f S := by
  obtain ⟨r,hr,L,hL⟩:=h
  exact ⟨r,hr.trans hRS,L,hL⟩

theorem full_linear_cells_constant (f : Q→A) :
    HasFullLinearCells (fun q (_ : V)=>f q) 0 :=
  ⟨0,le_rfl,0,fun _ _ _=>by simp⟩

theorem full_linear_cells_map {W : Type} [AddCommGroup W] [Module F W]
    [FiniteDimensional F W] (L : V→ₗ[F]W) :
    HasFullLinearCells (fun (_ : Q) x=>L x) (dim W) := by
  let E:W≃ₗ[F]Vec (Fin (dim W)):=(Module.finBasis F W).equivFun
  exact ⟨dim W,le_rfl,E.toLinearMap.comp L,fun _ x y=>E.injective.eq_iff.symm⟩

theorem full_linear_cells_postprocess {f : Q→V→A} {R : ℕ}
    (h : HasFullLinearCells f R) (ψ : Q→A→B) (hψ : ∀ q,Injective (ψ q)) :
    HasFullLinearCells (fun q x=>ψ q (f q x)) R := by
  obtain ⟨r,hr,L,hL⟩:=h
  exact ⟨r,hr,L,fun q x y=>(hψ q).eq_iff.trans (hL q x y)⟩

theorem full_linear_cells_bundle [Fintype T] {B : T→Type} (R : T→ℕ)
    (f : ∀ t,Q→V→B t) (h : ∀ t,HasFullLinearCells (f t) (R t)) :
    HasFullLinearCells (fun q x t=>f t q x) (∑ t,R t) := by
  classical
  choose r hr L hL using h
  let D:=Σ t,Fin (r t)
  let e:=Fintype.equivFin D
  let P : V→ₗ[F]Vec (Fin (Fintype.card D)) :=
    { toFun:=fun x j=>L (e.symm j).1 x (e.symm j).2
      map_add':=fun x y=>by ext j; simp only [map_add,Pi.add_apply]
      map_smul':=fun a x=>by ext j; simp only [map_smul,Pi.smul_apply,RingHom.id_apply] }
  refine ⟨Fintype.card D,?_,P,fun q x y=>?_⟩
  · simp only [D,Fintype.card_sigma,Fintype.card_fin]
    exact Finset.sum_le_sum fun t _=>hr t
  constructor
  · intro he
    ext j
    exact congrFun ((hL (e.symm j).1 q x y).mp (congrFun he (e.symm j).1)) (e.symm j).2
  · intro he
    funext t
    apply (hL t q x y).mpr
    funext j
    have hh:=congrFun he (e ⟨t,j⟩)
    change L (e.symm (e ⟨t,j⟩)).1 x (e.symm (e ⟨t,j⟩)).2=
      L (e.symm (e ⟨t,j⟩)).1 y (e.symm (e ⟨t,j⟩)).2 at hh
    rw [e.symm_apply_apply] at hh
    exact hh

end
end Lax793645Proofs.Simplifications
