import Lax793645Proofs.Simplifications.OneFrozenTables
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.FiniteTableEnumeration

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix Finset LinearMap Submodule Module Function
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n : ℕ}

def oneChannelInjection (p : Shape) (n : ℕ) : (Bool→Hyperbolic p.h)→ₗ[F]Vec (OneColumn p n):=
  (oneNominalCoordinates p n).symm.toLinearMap.comp (LinearMap.inr F _ _)
def oneAllChannels (p : Shape) (n : ℕ):=LinearMap.range (oneChannelInjection p n)
def oneTabSpace (a : ImagePlan (Comp p.g) (OneColumn p n)) (e : Comp p.g):=
  a e⊔oneAllChannels p n

theorem one_channel_space_dim : dim (oneAllChannels p n)≤4*p.h := by
  apply (LinearMap.finrank_range_le _).trans_eq
  simp [dim,Module.finrank_pi_fintype,Hyperbolic,Module.finrank_prod,dim_vec,
    Fintype.sum_bool]
  omega

theorem one_tab_space_dim (a : ImagePlan (Comp p.g) (OneColumn p n)) (e : Comp p.g) :
    dim (oneTabSpace a e)≤dim (a e)+4*p.h := by
  have hh:=Submodule.finrank_sup_add_finrank_inf_eq (a e) (oneAllChannels p n)
  change dim (a e⊔oneAllChannels p n : Space (Vec (OneColumn p n)))+
    dim (a e⊓oneAllChannels p n : Space (Vec (OneColumn p n)))=
    dim (a e)+dim (oneAllChannels p n) at hh
  have hg:=one_channel_space_dim (p:=p) (n:=n)
  change dim (a e⊔oneAllChannels p n : Space (Vec (OneColumn p n)))≤_
  omega

def oneFitsTable (a b : ImagePlan (Comp p.g) (OneColumn p n)) (T Q : OneCross p n) :=
  ∀ e,∀ v∈oneTabSpace a e,∀ w∈oneTabSpace b e,evmat (T e) v w=evmat (Q e) v w

theorem one_fits_table_reciprocal (a b : ImagePlan (Comp p.g) (OneColumn p n))
    (T Q : OneCross p n) (h : oneFitsTable a b T Q) :
    oneFitsTable b a (fun e=>(T e)ᵀ) (fun e=>(Q e)ᵀ) := by
  intro e v hv w hw
  rw [evmat_transpose,evmat_transpose]
  exact h e w hw v hv

abbrev OneCouponDeck (a b : ImagePlan (Comp p.g) (OneColumn p n)) :=
  ∀ e : Comp p.g,Mat (Fin (dim (oneTabSpace a e))) (Fin (dim (oneTabSpace b e)))

def oneNomen (a b : ImagePlan (Comp p.g) (OneColumn p n)) (v : OneCross p n) :
    OneCouponDeck a b:=fun e=>pullM (pack (oneTabSpace a e)) (pack (oneTabSpace b e)) (v e)

theorem one_nomen_fits (a b : ImagePlan (Comp p.g) (OneColumn p n)) (x y : OneCross p n)
    (h : oneNomen a b x=oneNomen a b y) : oneFitsTable a b x y := by
  intro e v hv w hw
  obtain ⟨u,rfl⟩:∃ u,pack (oneTabSpace a e)*ᵥu=v:=(pack_mem_iff ..).mp hv
  obtain ⟨z,rfl⟩:∃ z,pack (oneTabSpace b e)*ᵥz=w:=(pack_mem_iff ..).mp hw
  simp_rw [←evmat_pull]
  exact congrArg (fun A=>evmat A u z) (congrFun h e)

def oneDeckMax (p : Shape) (K : ℕ):=Fintype.card (Comp p.g)*(K+4*p.h)^2

theorem one_deck_cap (a b : ImagePlan (Comp p.g) (OneColumn p n)) (K : ℕ)
    (ha : ∀ e,dim (a e)≤K) (hb : ∀ e,dim (b e)≤K) :
    Fintype.card (OneCouponDeck a b)≤2^oneDeckMax p K := by
  have ht : dim (OneCouponDeck a b)=∑ e:Comp p.g,dim (oneTabSpace a e)*dim (oneTabSpace b e) := by
    unfold OneCouponDeck dim
    rw [Module.finrank_pi_fintype]
    apply sum_congr rfl
    intro e _
    rw [show Module.finrank F _=_ from dim_mat (Fin (dim (oneTabSpace a e)))
      (Fin (dim (oneTabSpace b e))),Fintype.card_fin,Fintype.card_fin]
  have he (e : Comp p.g) : dim (oneTabSpace a e)*dim (oneTabSpace b e)≤(K+4*p.h)^2 := by
    rw [pow_two]
    exact Nat.mul_le_mul ((one_tab_space_dim a e).trans (Nat.add_le_add_right (ha e) _))
      ((one_tab_space_dim b e).trans (Nat.add_le_add_right (hb e) _))
  have hd : dim (OneCouponDeck a b)≤oneDeckMax p K:=ht ▸
    (sum_le_sum (fun e _=>he e)).trans_eq (by simp [oneDeckMax])
  have hc:=card_space (OneCouponDeck a b)
  have hh : (Fintype.card (OneCouponDeck a b):ℝ)≤2^oneDeckMax p K:=hc.le.trans
    ((bp_le (by exact_mod_cast hd)).trans_eq (bp_nat _))
  exact_mod_cast hh

/-- Enumerate only restrictions to the stored pins and the channel
coordinates. The table count is fixed independently of n. -/
theorem one_deck_cast (a b : ImagePlan (Comp p.g) (OneColumn p n)) (K : ℕ)
    (ha : ∀ e,dim (a e)≤K) (hb : ∀ e,dim (b e)≤K) :
    ∃ T : Fin (2^oneDeckMax p K)→OneCross p n,∀ Q,∃ i,oneFitsTable a b (T i) Q := by
  let A:=OneCouponDeck a b
  let f:=oneNomen a b
  choose w hw using fun x:A=>show ∃ y:OneCross p n,∀ z,f z=x→f y=x from by
    by_cases h:∃ z,f z=x
    · obtain ⟨z,hz⟩:=h
      exact ⟨z,fun _ _=>hz⟩
    exact ⟨0,fun z hz=>(h ⟨z,hz⟩).elim⟩
  let t:=Fintype.card A
  let E:=Fintype.equivFin A
  let T (i : Fin (2^oneDeckMax p K)):=if h:i.val<t then w (E.symm ⟨i.val,h⟩) else 0
  have ht:t≤2^oneDeckMax p K:=one_deck_cap a b K ha hb
  refine ⟨T,fun Q=>?_⟩
  let i:=E (f Q)
  let j:Fin (2^oneDeckMax p K):=Fin.castLE ht i
  refine ⟨j,one_nomen_fits a b _ _ ?_⟩
  change f (T j)=f Q
  unfold T
  rw [dif_pos (show j.val<t from i.isLt)]
  change f (w (E.symm (E (f Q))))=f Q
  rw [Equiv.symm_apply_apply]
  exact hw _ _ rfl

end
end Lax793645Proofs.Simplifications
