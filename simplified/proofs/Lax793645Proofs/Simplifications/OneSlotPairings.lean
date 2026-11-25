import Lax793645Proofs.Simplifications.OneQueryFreeRows

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open LinearMap Module Function Finset Matrix
open scoped Classical BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
  {p : Shape} {n N : ℕ}

def hyperbolicSlotPairing : LinearMap.BilinForm F (E→Vec (HyperbolicIdx N)):=
  ∑ e,(hyperbolicMatrix N).toQuadraticForm'.polarBilin.compl₁₂
    (LinearMap.proj e) (LinearMap.proj e)

theorem hyperbolic_slot_pairing_apply (x y : E→Vec (HyperbolicIdx N)) :
    hyperbolicSlotPairing x y=
      ∑ e,(hyperbolicMatrix N).toQuadraticForm'.polarBilin (x e) (y e) := by
  simp only [hyperbolicSlotPairing,LinearMap.sum_apply,LinearMap.compl₁₂_apply,
    LinearMap.proj_apply]

theorem hyperbolic_slot_pairing_nondegenerate :
    (hyperbolicSlotPairing (E:=E) (N:=N)).Nondegenerate := by
  have hs (x y : E→Vec (HyperbolicIdx N)) :
      hyperbolicSlotPairing x y=hyperbolicSlotPairing y x:=by
    simp only [hyperbolic_slot_pairing_apply,binary_polar_symm (hyperbolicMatrix N).toQuadraticForm']
  have hl (x : E→Vec (HyperbolicIdx N)) (h : ∀ y,hyperbolicSlotPairing x y=0) : x=0 := by
    funext e
    apply (hyperbolic_matrix_nondegenerate N).1
    intro z
    have hh:=h (Pi.single e z)
    simpa only [hyperbolic_slot_pairing_apply,Pi.single_apply,apply_ite,map_zero,
      Finset.sum_ite_eq',mem_univ,if_true] using hh
  exact ⟨hl,fun x h=>hl x (fun y=>(hs x y).trans (h y))⟩

def oneSlotFreeColumns (v : Template p I) (o : OneUnit p n N) :
    (I→Vec (Fin n))→ₗ[F]OneSlotKeys v.t N:=
  LinearMap.pi (fun s=>((o (v.aim s.1) s.2.val).comp
    (oneFreeColumns p n (v.s s.1))).comp (LinearMap.proj s.1))

theorem one_slot_slice_sum (t : Tagging p I) (i : I)
    (x : OneSlotKeys t N) (y : OneJointKey p N) :
    oneKeyPairing (oneSlotSlice t i x) y=
      ∑ e : TagStar (t i),(hyperbolicMatrix N).toQuadraticForm'.polarBilin (x ⟨i,e⟩) (y e.val) := by
  let f (e : Comp p.g):=(hyperbolicMatrix N).toQuadraticForm'.polarBilin
    (oneSlotSlice t i x e) (y e)
  have hs : (∑ e : TagStar (t i),f e.val)=∑ e : Comp p.g,f e := by
    rw [←Finset.sum_subtype (univ.filter (fun e=>inc e (t i))) (by intro e; simp) f]
    apply Finset.sum_subset (subset_univ _)
    intro e _ he
    have hn : ¬inc e (t i):=fun h=>he (mem_filter.mpr ⟨mem_univ _,h⟩)
    simp only [f,oneSlotSlice,LinearMap.pi_apply,dif_neg hn,LinearMap.zero_apply,map_zero,
      LinearMap.zero_apply]
  rw [one_key_pairing_apply,←hs]
  apply Finset.sum_congr rfl
  intro e _
  simp only [f,one_slot_slice_at]

theorem one_slot_free_pairing (v : Template p I) [DecidableEq (KeySlots p v.t)]
    (o : OneUnit p n N) (x : OneSlotKeys v.t N) (z : I→Vec (Fin n)) :
    hyperbolicSlotPairing x (oneSlotFreeColumns v o z)=
      ∑ i,oneTupleFreeRows v o x i (z i) := by
  rw [hyperbolic_slot_pairing_apply,Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  change (∑ e : TagStar (v.t i),_)=
    oneMixedRow (oneFreeColumns p n (v.s i)) (o (v.aim i)) (oneSlotSlice v.t i x) (z i)
  rw [←one_free_pairing,one_slot_slice_sum]
  rfl

theorem one_slot_row_kernel (v : Template p I) [DecidableEq (KeySlots p v.t)]
    (o : OneUnit p n N) {D : Type} [AddCommGroup D] [Module F D]
    (T : D→ₗ[F]OneSlotKeys v.t N) :
    (((oneSlotFreeColumns v o).dualMap.comp hyperbolicSlotPairing).comp T).ker=
      ((oneTupleFreeRows v o).comp T).ker := by
  ext x
  simp only [LinearMap.mem_ker]
  constructor
  · intro h
    apply funext
    intro i
    apply LinearMap.ext
    intro z
    change oneTupleFreeRows v o (T x) i z=0
    have hh:=LinearMap.congr_fun h (Pi.single i z)
    change hyperbolicSlotPairing (T x) (oneSlotFreeColumns v o (Pi.single i z))=0 at hh
    rw [one_slot_free_pairing] at hh
    simpa only [Pi.single_apply,apply_ite,map_zero,sum_ite_eq',mem_univ,if_true] using hh
  · intro h
    apply LinearMap.ext
    intro z
    change hyperbolicSlotPairing (T x) (oneSlotFreeColumns v o z)=0
    rw [one_slot_free_pairing]
    apply Finset.sum_eq_zero
    intro i _
    exact LinearMap.congr_fun (congrFun h i) (z i)

end
end Lax793645Proofs.Simplifications
