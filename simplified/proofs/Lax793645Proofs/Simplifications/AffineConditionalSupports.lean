import Lax793645Proofs.Simplifications.ConditionalStatusSupports
import Lax793645Proofs.Simplifications.QueryCellRecentring

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open LinearMap Function Finset
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {V C S : Type} [AddCommGroup V] [Module F V] [Fintype V]
  [AddCommGroup C] [Module F C] [Fintype C]

/-- Recentring a uniform input gives the exact conditional law on a
linear cell, including its normalization. -/
theorem affine_recenter_conditional (L : V→ₗ[F]C) (k : C) (s : C→ₗ[F]V)
    (hs : ∀ c,L (s c)=c) (c : C) :
    mapW unif (fun x=>affineRecenter L k s x c)=unifOn (fun x=>L x+k=c) := by
  classical
  let f:=fun x=>affineRecenter L k s x c
  have hf (x : V): L (f x)+k=c:=by
    simp only [f,affineRecenter,map_add,hs]
    abel
  rw [←unifOn_true]
  apply uniform_orbit f ⟨0,trivial⟩ (fun x _=>hf x)
  intro y z hy hz
  let e:V≃V:=⟨fun x=>x+(z-y),fun x=>x+(z-y),add_polar _,add_polar _⟩
  have hd : L (z-y)=0:=by
    rw [map_sub,add_right_cancel (hz.trans hy.symm),sub_self]
  have he (x : V): f (e x)=f x+(z-y):=by
    change affineRecenter L k s (x+(z-y)) c=affineRecenter L k s x c+(z-y)
    simp only [affineRecenter,map_add,hd,add_zero]
    abel
  refine ⟨e,fun _=>Iff.rfl,fun x=>?_⟩
  rw [he]
  constructor
  · intro hx
    rw [hx]
    abel
  · intro hx
    apply add_right_cancel (b:=z-y)
    rw [hx]
    abel

/-- A bounded coordinate description survives conditioning on any
number of full linear key coordinates. The new description still uses
only the original status budget. -/
theorem affine_conditional_status_factorization (L : V→ₗ[F]C) (k : C)
    (s : C→ₗ[F]V) (hs : ∀ c,L (s c)=c) (f : V→S) (m : ℕ)
    (hf : HasLinearCells (fun (_ : Unit) x=>f x) m) :
    ∃ A : C→ₗ[F]Vec (Fin m),∃ B : V→ₗ[F]Vec (Fin m),∃ d : Vec (Fin m),
      ∃ φ : Vec (Fin m)→S,∀ v c,
        pr (unifOn (fun x=>L x+k=c)) (fun x=>f x=v)=conditionalStatus A B d φ v c := by
  obtain ⟨T,φ,hφ⟩:=linear_cells_exact hf
  let A:=T.comp s
  let B:=T.comp (LinearMap.id-s.comp L)
  let d:Vec (Fin m):= -T (s k)
  refine ⟨A,B,d,φ (),fun v c=>?_⟩
  rw [←affine_recenter_conditional L k s hs c,mapW_pr]
  unfold conditionalStatus
  unfold pr
  apply avg_congr
  intro x _
  change ind (f (affineRecenter L k s x c)=v)=ind (φ () (A c+B x+d)=v)
  rw [hφ ()]
  have he : T (affineRecenter L k s x c)=A c+B x+d:=by
    simp only [affineRecenter,A,B,d,LinearMap.comp_apply,LinearMap.sub_apply,
      LinearMap.id_apply,map_add,map_sub]
    abel
  rw [he]

/-- The gap is for the actual normalized conditional distributions,
not just for an auxiliary table. -/
theorem affine_conditional_overlap_gap {V' S' : Type}
    [AddCommGroup V'] [Module F V'] [Fintype V']
    (L : V→ₗ[F]C) (L' : V'→ₗ[F]C) (k k' : C)
    (s : C→ₗ[F]V) (s' : C→ₗ[F]V')
    (hs : ∀ c,L (s c)=c) (hs' : ∀ c,L' (s' c)=c)
    (f : V→S) (f' : V'→S') (m : ℕ)
    (hf : HasLinearCells (fun (_ : Unit) x=>f x) m)
    (hf' : HasLinearCells (fun (_ : Unit) x=>f' x) m)
    (v : S) (v' : S') (ν : Wgt C) (hν : ∀ c,unif c/2≤ν c) :
    let overlap:=avg ν (fun c=>
      pr (unifOn (fun x=>L x+k=c)) (fun x=>f x=v)*
      pr (unifOn (fun x=>L' x+k'=c)) (fun x=>f' x=v'))
    overlap=0 ∨ bp (-(4*(m:ℝ)+1))≤overlap := by
  obtain ⟨A,B,d,φ,hφ⟩:=affine_conditional_status_factorization L k s hs f m hf
  obtain ⟨A',B',d',φ',hφ'⟩:=affine_conditional_status_factorization L' k' s' hs' f' m hf'
  dsimp only
  simp_rw [hφ,hφ']
  exact conditional_status_overlap_gap m A A' B B' d d' φ φ' v v' ν hν

/-- Conditioning on a bit already recorded in a status cannot decrease
the probability of that status when the bit agrees. -/
theorem status_conditioning_dominates {A T : Type} [Fintype A]
    (μ : Wgt A) (hμ : IsLaw μ) (f : A→T) (q : T→F) (v : T) :
    pr μ (fun x=>f x=v)≤pr (onW μ (fun x=>q (f x)=q v)) (fun x=>f x=v) := by
  have he : (fun x=>q (f x)=q v ∧ f x=v)=(fun x=>f x=v):=by
    funext x
    exact propext ⟨And.right,fun hx=>⟨congrArg q hx,hx⟩⟩
  have hh:=pr_of_on hμ.nz (fun x=>q (f x)=q v) (fun x=>f x=v)
  rw [he] at hh
  rw [hh]
  exact mul_le_of_le_one_left (pr_nonneg (normW_nonneg (subW_nonneg hμ.nz _)))
    ((pr_le_tot hμ.nz).trans_eq hμ.total)

/-- The overlap gap also survives the prescribed diagonal bit. Its
normalization introduces no dependence on the size of the partition. -/
theorem affine_scoped_overlap_gap {V' S' : Type}
    [AddCommGroup V'] [Module F V'] [Fintype V']
    (L : V→ₗ[F]C) (L' : V'→ₗ[F]C) (k k' : C)
    (s : C→ₗ[F]V) (s' : C→ₗ[F]V')
    (hs : ∀ c,L (s c)=c) (hs' : ∀ c,L' (s' c)=c)
    (f : V→S) (f' : V'→S') (m : ℕ)
    (hf : HasLinearCells (fun (_ : Unit) x=>f x) m)
    (hf' : HasLinearCells (fun (_ : Unit) x=>f' x) m)
    (q : S→F) (q' : S'→F) (v : S) (v' : S')
    (ν : Wgt C) (hν : ∀ c,unif c/2≤ν c) :
    let overlap:=avg ν (fun c=>
      pr (onW (unifOn (fun x=>L x+k=c)) (fun x=>q (f x)=q v)) (fun x=>f x=v)*
      pr (onW (unifOn (fun x=>L' x+k'=c)) (fun x=>q' (f' x)=q' v')) (fun x=>f' x=v'))
    overlap=0 ∨ bp (-(4*(m:ℝ)+1))≤overlap := by
  let h (c : C):=pr (unifOn (fun x=>L x+k=c)) (fun x=>f x=v)
  let h' (c : C):=pr (unifOn (fun x=>L' x+k'=c)) (fun x=>f' x=v')
  let g (c : C):=pr (onW (unifOn (fun x=>L x+k=c)) (fun x=>q (f x)=q v)) (fun x=>f x=v)
  let g' (c : C):=pr (onW (unifOn (fun x=>L' x+k'=c)) (fun x=>q' (f' x)=q' v')) (fun x=>f' x=v')
  have hμ c:IsLaw (unifOn (fun x=>L x+k=c)):=unifOn_law ⟨s (c-k),by rw [hs,sub_add_cancel]⟩
  have hμ' c:IsLaw (unifOn (fun x=>L' x+k'=c)):=unifOn_law ⟨s' (c-k'),by rw [hs',sub_add_cancel]⟩
  have hg c:h c≤g c:=status_conditioning_dominates _ (hμ c) f q v
  have hg' c:h' c≤g' c:=status_conditioning_dominates _ (hμ' c) f' q' v'
  have hn c:0≤ν c:=(div_nonneg (unif_law.nz c) (by norm_num)).trans (hν c)
  have hz c:h c=0 → g c=0:=by
    intro hc
    change pr (onW _ _) _=0
    rw [pr_on]
    have he : (fun x=>q (f x)=q v ∧ f x=v)=(fun x=>f x=v):=by
      funext x
      exact propext ⟨And.right,fun hx=>⟨congrArg q hx,hx⟩⟩
    rw [he]
    change h c / _=0
    rw [hc,zero_div]
  have hz' c:h' c=0 → g' c=0:=by
    intro hc
    change pr (onW _ _) _=0
    rw [pr_on]
    have he : (fun x=>q' (f' x)=q' v' ∧ f' x=v')=(fun x=>f' x=v'):=by
      funext x
      exact propext ⟨And.right,fun hx=>⟨congrArg q' hx,hx⟩⟩
    rw [he]
    change h' c / _=0
    rw [hc,zero_div]
  rcases affine_conditional_overlap_gap L L' k k' s s' hs hs' f f' m hf hf' v v' ν hν with hzero|hpos
  · left
    change avg ν (fun c=>g c*g' c)=0
    apply Finset.sum_eq_zero
    intro c _
    change ν c*(g c*g' c)=0
    have hc : ν c*(h c*h' c)=0:=
      (Finset.sum_eq_zero_iff_of_nonneg (fun c _=>mul_nonneg (hn c)
        (mul_nonneg (pr_nonneg (hμ c).nz) (pr_nonneg (hμ' c).nz)))).mp hzero c (mem_univ c)
    rcases mul_eq_zero.mp hc with hv|hc
    · rw [hv,zero_mul]
    rcases mul_eq_zero.mp hc with hc|hc
    · rw [hz c hc,zero_mul,mul_zero]
    · rw [hz' c hc,mul_zero,mul_zero]
  · right
    exact hpos.trans (avg_mono hn (fun c=>mul_le_mul (hg c) (hg' c)
      (pr_nonneg (hμ' c).nz) ((pr_nonneg (hμ c).nz).trans (hg c))))

end
end Lax793645Proofs.Simplifications
