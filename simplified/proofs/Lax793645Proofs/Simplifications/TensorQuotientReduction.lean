import Lax793645Proofs.Simplifications.TensorAtomIsolation

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix Submodule Module LinearMap
open scoped BigOperators
noncomputable section

variable {S T I X : Type} [Fintype S] [Fintype T] [Fintype I] [Fintype X]

theorem annih_antitone {U V : Space (Vec X)} (h : U ≤ V) : annih V ≤ annih U := by
  intro x hx
  rw [annih_mem] at hx ⊢
  exact fun y hy => hx y (h hy)

theorem annih_sup_eq (U V : Space (Vec X)) : annih (U ⊔ V)=annih U ⊓ annih V := by
  apply le_antisymm
  · exact le_inf (annih_antitone le_sup_left) (annih_antitone le_sup_right)
  intro x hx
  rw [annih_mem]
  intro y hy
  obtain ⟨u,hu,v,hv,rfl⟩ := Submodule.mem_sup.mp hy
  rw [dotProduct_add,(annih_mem ..).mp hx.1 u hu,(annih_mem ..).mp hx.2 v hv,add_zero]

theorem annih_inf_eq (U V : Space (Vec X)) : annih (U ⊓ V)=annih U ⊔ annih V := by
  have h := annih_sup_eq (annih U) (annih V)
  rw [annih_annih,annih_annih] at h
  rw [←h,annih_annih]

theorem evmat_annih_column (w : Mat X X) (x y : Vec X) (hx : x ∈ annih (colSp w)) :
    evmat w x y=0 :=
  (annih_mem ..).mp hx (w *ᵥ y) ⟨y,rfl⟩

/-- Quotient vanishing can first be restricted to the column space. This is
the intersection step needed before replacing low-rank pin vectors by their
protected rectangle. -/
theorem vanish_column_intersections (w : Mat X X) (hw : wᵀ=w)
    (P Q : Space (Vec X)) (hv : vanish P Q w) :
    vanish (colSp w ⊓ P) (colSp w ⊓ Q) w := by
  intro x hx y hy
  rw [annih_inf_eq,Submodule.mem_sup] at hx hy
  obtain ⟨a,ha,b,hb,rfl⟩ := hx
  obtain ⟨c,hc,d,hd,rfl⟩ := hy
  change dotProduct (a+b) (w *ᵥ (c+d))=0
  rw [Matrix.mulVec_add,add_dotProduct,dotProduct_add,dotProduct_add]
  have hac : evmat w a c=0 := evmat_annih_column w a c ha
  have had : evmat w a d=0 := evmat_annih_column w a d ha
  have hbc : evmat w b c=0 := by
    rw [←evmat_transpose,hw]
    exact evmat_annih_column w c b hc
  change evmat w a c+evmat w a d+(evmat w b c+evmat w b d)=0
  rw [hac,had,hbc,hv b hb d hd]; simp

theorem vanish_enlarge (w : Mat X X) {P Q P' Q' : Space (Vec X)}
    (hv : vanish P Q w) (hP : P ≤ P') (hQ : Q ≤ Q') : vanish P' Q' w :=
  fun x hx y hy => hv x (annih_antitone hP hx) y (annih_antitone hQ hy)

theorem selected_reshape_rank (s : I → Vec S) (t : I → Vec T)
    (x : Vec (S × T)) (hx : x ∈ selectedTensorSpace s t) :
    Matrix.rank (flattenMatrix.symm x) ≤ Fintype.card I := by
  let U := Submodule.span F (Set.range s)
  have hle : selectedTensorSpace s t ≤ tensorRectangle U ⊤ := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact tensorRay_rectangle U ⊤ _ _ (Submodule.subset_span ⟨i,rfl⟩) Submodule.mem_top
  obtain ⟨M,hM,hMx⟩ := hle hx
  have he : flattenMatrix.symm x=M := by rw [←hMx]; rfl
  rw [he]
  exact (Submodule.finrank_mono ((box_mem ..).mp hM).1).trans (finrank_range_le_card (R:=F) s)

/-- Only the original component's rank is used here. Subtracting the atoms
later may increase matrix rank, so no rank estimate is carried to that step. -/
theorem low_rank_intersection_protected
    (w : Mat (S × T) (S × T))
    (hsym : ∀ a b i j, w (a,i) (b,j)=w (a,j) (b,i))
    (s : I → Vec S) (t : I → Vec T)
    (P D : Space (Vec (S × T)))
    (hP : ∀ x ∈ P, Matrix.rank (flattenMatrix.symm x) ≤ w.rank^2+Fintype.card I → x ∈ D) :
    colSp w ⊓ (P ⊔ selectedTensorSpace s t) ≤ D ⊔ selectedTensorSpace s t := by
  rintro x ⟨hx,hxP⟩
  obtain ⟨p,hp,a,ha,hxpa⟩ := Submodule.mem_sup.mp hxP
  have hh : Matrix.rank (flattenMatrix.symm x) ≤ w.rank^2 := reshape_rank_le w hsym x hx
  have hA := selected_reshape_rank s t a ha
  have he : p=x+a := by
    rw [←hxpa,add_assoc,char_two,add_zero]
  have hpr : Matrix.rank (flattenMatrix.symm p) ≤ w.rank^2+Fintype.card I := by
    rw [he,map_add]
    exact (mrk_add_le ..).trans (Nat.add_le_add hh hA)
  exact Submodule.mem_sup.mpr ⟨p,hP p hp hpr,a,ha,hxpa⟩

theorem protected_quotient_vanish (w : Mat (S × T) (S × T)) (hw : wᵀ=w)
    (hsym : ∀ a b i j, w (a,i) (b,j)=w (a,j) (b,i))
    (s : I → Vec S) (t : I → Vec T)
    (P Q D : Space (Vec (S × T)))
    (hP : ∀ x ∈ P, Matrix.rank (flattenMatrix.symm x) ≤ w.rank^2+Fintype.card I → x ∈ D)
    (hQ : ∀ x ∈ Q, Matrix.rank (flattenMatrix.symm x) ≤ w.rank^2+Fintype.card I → x ∈ D)
    (hv : vanish (P ⊔ selectedTensorSpace s t) (Q ⊔ selectedTensorSpace s t) w) :
    vanish (D ⊔ selectedTensorSpace s t) (D ⊔ selectedTensorSpace s t) w :=
  vanish_enlarge w (vanish_column_intersections w hw _ _ hv)
    (low_rank_intersection_protected w hsym s t P D hP)
    (low_rank_intersection_protected w hsym s t Q D hQ)

end
end Lax793645Proofs.Simplifications
