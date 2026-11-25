import Lax793645Proofs.Simplifications.OneStatusRecipes

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis Finset Matrix LinearMap
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N : ℕ} {I : Type} [Fintype I]

private theorem one_B1_eval {v : Volley p n I} {s : Script p I}
    (t : Tagging p I) (m : Mixer p n) (ha : v.reads s m)
    {x y : I} (hg : x≠y) (hh : v.obj x=v.obj y) :
    B1 m (v.atomAt t x) (v.atomAt t y)=prescribedB p t s x y := by
  classical
  change ∑ i : Fin p.J, _ = _
  refine Finset.sum_congr rfl fun i _=>Finset.sum_congr rfl fun e _=>
    Finset.sum_congr rfl fun f _=>?_
  by_cases he : inc e (t x)
  · by_cases hf : inc f (t y)
    · rw [if_pos ⟨he,hf⟩,ha x y hg hh,ha x y hg hh]
      simp only [Volley.atomAt,atom_def,he,hf,ite_true,mom,liftM_outer,pair_outers]
      rfl
    rw [if_neg (show ¬ (_ ∧ _) from fun h=>hf h.2)]
    simp only [Volley.atomAt,atom_def,hf,ite_false,map_zero]
  rw [if_neg (show ¬ (_ ∧ _) from fun h=>he h.1)]
  simp only [Volley.atomAt,atom_def,he,ite_false]
  rw [mpair_comm,map_zero]

theorem one_grads_by_script (v w : Volley p n I) (t : Tagging p I) (m : Mixer p n)
    (y : OneUnit p n N) {d f : Vec I} {u : Mat I I} {s : Script p I}
    (h : fulfills p t d f u s v.obj w.obj) (hs : v.reads s m)
    (hd : ∀ x,role p n (v.atomAt t x)=d x)
    (hf : ∀ x,oneInner y (w.obj x) (w.atomAt t x)=f x)
    (hu : ∀ x y : I,T0 p n (v.atomAt t x) (v.atomAt t y)=u x y) :
    oneAttackGrad v w t m y := by
  classical
  intro x j
  rw [grad_val,hd,hf,Volley.sumAt,map_sum,LinearMap.sum_apply]
  rw [←h x j]
  congr 1
  refine Finset.sum_congr rfl fun i hi=>?_
  unfold prescribedT
  split
  · rename_i he
    subst x
    rw [T_diag,hd]
  rename_i he
  have hx:=(Finset.mem_filter.mp hi).2.1
  rw [Tsym_val,hu,one_B1_eval t m hs he hx,one_B1_eval t m hs (Ne.symm he) hx.symm]

variable {q : Format} {d e : Rates}

theorem one_tmill_formula {b} (t : Tagging p (Messenger q)) (hg : Odd p.g)
    (v : Charts p n d) (l f) (x : Inputs p n (Messenger q)) (m : Mixer p n)
    (o : OneUnit p n N) (a : Amounts p q d b) (h : onePrinted b v t l f m o x=a)
    (i j : Messenger q) :
    T0 p n (useAtom p (t i) (l i) (f i) (x i)) (useAtom p (t j) (l j) (f j) (x j))=
      TMill p t a i j := by
  classical
  rw [←h]
  simp_rw [T0_val,roleT_scan,sharedT_scan _ hg]
  rfl

theorem one_procl_grad (t : Tagging p (Messenger q)) {b}
    (a : Amounts p q d b) (w : Amounts p q e (!b))
    (hg : Odd p.g) (v : Charts p n d) (v' : Charts p n e)
    (l f l' f') (x y : Inputs p n (Messenger q)) (m : Mixer p n)
    (o z : OneUnit p n N) (h : onePrinted b v t l f m o x=a)
    (hz : onePrinted (!b) v' t l' f' m z y=w)
    (s : Script p (Messenger q)) (hs : proclaims p a w t s) :
    let u:=(manager b t l f).draw x
    u.reads s m → oneAttackGrad u ((manager (!b) t l' f').draw y) t m z := by
  intro u hu
  apply one_grads_by_script u ((manager (!b) t l' f').draw y) t m z
    (d:=mailRole a) (f:=mailBias w) (u:=TMill p t a) (s:=s) hs hu
  · rw [←h]
    intro
    rfl
  · rw [←hz]
    intro
    rfl
  exact one_tmill_formula t hg v l f x m o a h

theorem one_rhyme_match (t : Tagging p (Messenger q))
    (a : Amounts p q d true) (w : Amounts p q e false)
    (v : Charts p n d) (v' : Charts p n e)
    (l f l' f') (x y : Inputs p n (Messenger q)) (m : Mixer p n)
    (o z : OneUnit p n N) (h : onePrinted true v t l f m o x=a)
    (hz : onePrinted false v' t l' f' m z y=w) (he : rhyme a w) :
    let u:=(manager true t l f).draw x
    u.roleMatch ((manager false t l' f').draw y) t := by
  classical
  intro u i j
  let s:=(manager false t l' f').draw y
  have hh : u.sumAt t s.obj i j=unionAt (u.atomAt t) (i,j):=
    sumAtSend true u t (i,j) rfl
  have hf : s.sumAt t u.obj j i=unionAt (s.atomAt t) (i,j):=
    sumAtSend false s t (i,j) rfl
  change _+role _ _ (s.sumAt _ _ _ _)=_
  rw [hh,hf]
  specialize he (i,j)
  change (funds a (i,j)).1.1+(funds w (i,j)).1.1=1 at he
  rw [one_funds_reg t true v m o l f x a h,
    one_funds_reg t false v' m z l' f' y w hz] at he
  exact he

end
end Lax793645Proofs.Simplifications
