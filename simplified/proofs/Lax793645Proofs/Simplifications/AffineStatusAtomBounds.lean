import Lax793645Proofs.Simplifications.FullCellStatusTables

/-! A nonzero status probability on any affine fiber has a fixed lower bound. No surjectivity onto all cells is assumed. -/

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Function LinearMap Finset Filter
open scoped Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {V C S : Type} [AddCommGroup V] [Module F V] [Fintype V]
  [AddCommGroup C] [Module F C]

theorem affine_fiber_status_gap
    (L : V→ₗ[F]C) (k c : C) (f : V→S) (m : ℕ)
    (hf : HasLinearCells (fun (_ : Unit) x=>f x) m)
    (hc : ∃ x,L x+k=c) (v : S)
    (hpos : 0<pr (unifOn (fun x=>L x+k=c)) (fun x=>f x=v)) :
    bp (-(m:ℝ))≤pr (unifOn (fun x=>L x+k=c)) (fun x=>f x=v) := by
  classical
  obtain ⟨x,hx⟩:=hc
  let : Fintype (range L):=Fintype.ofFinite _
  obtain ⟨s,hs⟩:=L.rangeRestrict.exists_rightInverse_of_surjective L.range_rangeRestrict
  have hs' c : L.rangeRestrict (s c)=c:=LinearMap.congr_fun hs c
  obtain ⟨A,B,d,φ,hφ⟩:=affine_conditional_status_factorization
    L.rangeRestrict 0 s hs' f m hf
  have he : (fun y=>L.rangeRestrict y+0=L.rangeRestrict x)=(fun y=>L y+k=c) := by
    funext y
    simp only [add_zero,←hx]
    exact propext ⟨fun h=>congrArg (fun z : range L=>(z:C)+k) h,
      fun h=>Subtype.ext (add_right_cancel h)⟩
  have hg:=hφ v (L.rangeRestrict x)
  rw [he] at hg
  rw [hg] at hpos ⊢
  simpa only [dim_vec,Fintype.card_fin] using conditional_status_gap A B d φ v _ hpos

theorem affine_fiber_scoped_status_gap
    (L : V→ₗ[F]C) (k c : C) (f : V→S) (m : ℕ)
    (hf : HasLinearCells (fun (_ : Unit) x=>f x) m)
    (hc : ∃ x,L x+k=c) (q : S→F) (v : S)
    (hpos : 0<pr (onW (unifOn (fun x=>L x+k=c)) (fun x=>q (f x)=q v))
      (fun x=>f x=v)) :
    bp (-(m:ℝ))≤pr (onW (unifOn (fun x=>L x+k=c)) (fun x=>q (f x)=q v))
      (fun x=>f x=v) := by
  have hμ:=unifOn_law hc
  have he : (fun x=>q (f x)=q v ∧ f x=v)=(fun x=>f x=v) := by
    funext x
    exact propext ⟨And.right,fun hx=>⟨congrArg q hx,hx⟩⟩
  have hp : 0<pr (unifOn (fun x=>L x+k=c)) (fun x=>f x=v) := by
    by_contra hn
    have hz : pr (unifOn (fun x=>L x+k=c)) (fun x=>f x=v)=0:=
      le_antisymm (not_lt.mp hn) (pr_nonneg hμ.nz)
    rw [pr_on,he,hz,zero_div] at hpos
    exact lt_irrefl _ hpos
  exact (affine_fiber_status_gap L k c f m hf hc v hp).trans
    (status_conditioning_dominates _ hμ f q v)

theorem scoped_status_gap (f : V→S) (m : ℕ)
    (hf : HasLinearCells (fun (_ : Unit) x=>f x) m) (q : S→F) (v : S)
    (hpos : 0<pr (unifOn (fun x=>q (f x)=q v)) (fun x=>f x=v)) :
    bp (-(m:ℝ))≤pr (unifOn (fun x=>q (f x)=q v)) (fun x=>f x=v) := by
  have he : unifOn (fun x : V=>(0 : V→ₗ[F]V) x+0=0)=unif := by
    simp only [LinearMap.zero_apply,zero_add,unifOn_true]
  have hh:=affine_fiber_scoped_status_gap (0 : V→ₗ[F]V) 0 0 f m hf
    ⟨0,by simp⟩ q v
  rw [he,on_unif] at hh
  exact hh hpos

theorem stained_linear_status_gap {A : Type} [Fintype A]
    (L : V→ₗ[F]C) (cell : V→A)
    (hcell : ∀ x y,cell x=cell y ↔ L x=L y)
    (f : V→S) (m : ℕ) (hf : HasLinearCells (fun (_ : Unit) x=>f x) m)
    (q : S→F) (v : S) (a : A)
    (hpos : 0<pr (stained (unifOn (fun x=>q (f x)=q v)) cell a)
      (fun x=>f x=v)) :
    bp (-(m:ℝ))≤pr (stained (unifOn (fun x=>q (f x)=q v)) cell a)
      (fun x=>f x=v) := by
  let Q:=fun x=>q (f x)=q v
  by_cases hm : mapW (unifOn Q) cell a≠0
  · have hp : 0<mapW (unifOn Q) cell a:=
      lt_of_le_of_ne (pr_nonneg (unifOn_sub Q).nz) (Ne.symm hm)
    obtain ⟨x,hx,_⟩:=exists_of_pr_pos (unifOn_sub Q).nz hp
    have he : stained (unifOn Q) cell a=
        onW (unifOn (fun y=>L y+0=L x)) Q := by
      rw [stained,if_pos hm,unifOn_and,unifOn_and]
      congr 1
      funext y
      have hc : cell y=a ↔ L y=L x:=by rw [←hx]; exact hcell y x
      exact propext (by simp only [add_zero,←hc,and_comm])
    change 0<pr (stained (unifOn Q) cell a) (fun x=>f x=v) at hpos
    change bp (-(m:ℝ))≤pr (stained (unifOn Q) cell a) (fun x=>f x=v)
    rw [he] at hpos ⊢
    exact affine_fiber_scoped_status_gap L 0 (L x) f m hf
      ⟨x,add_zero _⟩ q v hpos
  · change 0<pr (stained (unifOn Q) cell a) (fun x=>f x=v) at hpos
    change bp (-(m:ℝ))≤pr (stained (unifOn Q) cell a) (fun x=>f x=v)
    rw [stained,if_neg hm] at hpos ⊢
    exact scoped_status_gap f m hf q v hpos

end
end Lax793645Proofs.Simplifications
