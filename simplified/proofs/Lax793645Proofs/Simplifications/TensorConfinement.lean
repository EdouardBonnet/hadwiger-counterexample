import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.MatrixRanks

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix Submodule Module
open scoped BigOperators
noncomputable section

variable {S T : Type} [Fintype S] [Fintype T]

/-- A base-coordinate slice of a vector in the product coordinate space. -/
def selectorSlice (i : T) : Vec (S × T) →ₗ[F] Vec S where
  toFun x a := x (a,i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Separate symmetry in the base indices confines every selector slice of
every column-space vector to one space of dimension at most the square of
the matrix rank. No symmetric rank factorization or moment decomposition is
needed. -/
theorem selector_confinement (w : Mat (S × T) (S × T))
    (hs : ∀ a b i j, w (a,i) (b,j)=w (a,j) (b,i)) :
    ∃ U : Space (Vec S), dim U ≤ w.rank^2 ∧
      ∀ x ∈ colSp w, ∀ i, selectorSlice i x ∈ U := by
  classical
  obtain ⟨v,hv,hspan,_⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq F (Set.range w.col)
  choose k hk using hv
  let C := Fin (finrank F (Submodule.span F (Set.range w.col)))
  let f (cd : C × C) : Vec S := selectorSlice (k cd.1).2 (w.col (k cd.2))
  let U := Submodule.span F (Set.range f)
  have hsp : Submodule.span F (Set.range (fun c : C => w.col (k c)))=colSp w := by
    simp_rw [hk]
    exact hspan.trans (Matrix.range_mulVecLin w).symm
  have hsli (c : C) (x : Vec (S × T)) (hx : x ∈ colSp w) :
      selectorSlice (k c).2 x ∈ U := by
    rw [← hsp] at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨d,rfl⟩ := hx
        exact Submodule.subset_span ⟨(c,d),rfl⟩
    | zero => simpa using U.zero_mem
    | add x y _ _ hx hy => simpa using U.add_mem hx hy
    | smul b x _ hx => simpa using U.smul_mem b hx
  refine ⟨U,?_,?_⟩
  · have hdim : dim U ≤ Fintype.card (C × C) := finrank_range_le_card (R:=F) f
    simpa only [Fintype.card_prod,Fintype.card_fin,C,
      ← Matrix.rank_eq_finrank_span_cols,pow_two] using hdim
  intro x hx i
  rw [← hsp] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨c,rfl⟩ := hx
      have he : selectorSlice i (w.col (k c)) =
          selectorSlice (k c).2 (w.col ((k c).1,i)) := by
        funext a
        exact hs a (k c).1 i (k c).2
      rw [he]
      exact hsli c _ (colSp_mem _)
  | zero => simpa using U.zero_mem
  | add x y _ _ hx hy => simpa using U.add_mem hx hy
  | smul b x _ hx => simpa using U.smul_mem b hx

/-- Reshaping a column-space vector as a selector-by-base matrix has small
rank; the containing selector space is common to the whole column space. -/
theorem reshape_rank_le (w : Mat (S × T) (S × T))
    (hs : ∀ a b i j, w (a,i) (b,j)=w (a,j) (b,i))
    (x : Vec (S × T)) (hx : x ∈ colSp w) :
    Matrix.rank ((fun a i => x (a,i)) : Mat S T) ≤ w.rank^2 := by
  obtain ⟨U,hU,hxU⟩ := selector_confinement w hs
  let M : Mat S T := fun a i => x (a,i)
  have hle : colSp M ≤ U := by
    rw [colSp,Matrix.range_mulVecLin]
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact hxU x hx i
  exact (Submodule.finrank_mono hle).trans hU

end
end Lax793645Proofs.Simplifications
