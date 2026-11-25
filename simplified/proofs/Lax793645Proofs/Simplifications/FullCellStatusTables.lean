import Lax793645Proofs.Simplifications.AffineConditionalSupports
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.ConditionalFlags
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.ConditionalProductLaws

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Function LinearMap Finset
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {V C A : Type} [Fintype V] [Fintype C] [Fintype A]

/-- The arbitrary fallback in a conditional table is never used on a
nonempty full cell. Conditioning on the status bit and on the cell
commutes exactly, including the normalizing factors. -/
theorem stained_full_cell (Q : V→Prop) (L : V→C) (ι : C→A)
    (hι : Injective ι) (c : C) (hc : ∃ x,Q x ∧ L x=c) :
    stained (unifOn Q) (ι ∘ L) (ι c)=
      onW (unifOn (fun x=>L x=c)) Q := by
  classical
  obtain ⟨x,hx,hc⟩:=hc
  have hmass : 0<unifOn Q x := by
    rw [unifOn_val,ind_one hx]
    apply div_pos zero_lt_one
    exact lt_of_lt_of_le (ind_one hx ▸ zero_lt_one)
      (weight_le_tot (fun y=>ind_nonneg (Q y)) x)
  have hpos : 0<mapW (unifOn Q) (ι ∘ L) (ι c) :=
    hmass.trans_le (weight_le_pr (unifOn_sub Q).nz (by change ι (L x)=ι c; rw [hc]))
  rw [stained,if_pos hpos.ne',unifOn_and,unifOn_and]
  congr 1
  funext y
  exact propext (by simp only [Function.comp_apply,hι.eq_iff,and_comm])

variable [AddCommGroup V] [Module F V] [AddCommGroup C] [Module F C]

/-- Reindexing full affine cells by any injective set of color labels
preserves the status-overlap gap. This is the interface used by the
existing finite tables. -/
theorem full_cell_status_overlap_gap {V' S T : Type}
    [AddCommGroup V'] [Module F V'] [Fintype V'] [Fintype S] [Fintype T]
    (L : V→ₗ[F]C) (L' : V'→ₗ[F]C) (k k' : C)
    (s : C→ₗ[F]V) (s' : C→ₗ[F]V')
    (hs : ∀ c,L (s c)=c) (hs' : ∀ c,L' (s' c)=c)
    (f : V→S) (f' : V'→T) (m : ℕ)
    (hf : HasLinearCells (fun (_ : Unit) x=>f x) m)
    (hf' : HasLinearCells (fun (_ : Unit) x=>f' x) m)
    (q : S→F) (q' : T→F) (v : S) (v' : T)
    (ι : C→A) (hι : Injective ι)
    (hc : ∀ c,∃ x,q (f x)=q v ∧ L x+k=c)
    (hc' : ∀ c,∃ x,q' (f' x)=q' v' ∧ L' x+k'=c)
    (ν : Wgt C) (hν : ∀ c,unif c/2≤ν c) :
    let table (a : A):=mapW
      (stained (unifOn (fun x=>q (f x)=q v)) (fun x=>ι (L x+k)) a) f
    let table' (a : A):=mapW
      (stained (unifOn (fun x=>q' (f' x)=q' v')) (fun x=>ι (L' x+k')) a) f'
    let overlap:=avg (mapW ν ι) (fun a=>table a v*table' a v')
    overlap=0 ∨ bp (-(4*(m:ℝ)+1))≤overlap := by
  dsimp only
  rw [mapW_avg]
  have ht (c : C) : stained (unifOn (fun x=>q (f x)=q v))
      (fun x=>ι (L x+k)) (ι c)=
      onW (unifOn (fun x=>L x+k=c)) (fun x=>q (f x)=q v) :=
    stained_full_cell _ (fun x=>L x+k) ι hι c (hc c)
  have ht' (c : C) : stained (unifOn (fun x=>q' (f' x)=q' v'))
      (fun x=>ι (L' x+k')) (ι c)=
      onW (unifOn (fun x=>L' x+k'=c)) (fun x=>q' (f' x)=q' v') :=
    stained_full_cell _ (fun x=>L' x+k') ι hι c (hc' c)
  simp_rw [ht,ht']
  exact affine_scoped_overlap_gap L L' k k' s s' hs hs' f f' m hf hf'
    q q' v v' ν hν

end
end Lax793645Proofs.Simplifications
