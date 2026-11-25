import Lax793645Proofs.Simplifications.OneInitialPreparation
import Lax793645Proofs.Simplifications.OnePairedCollisionBounds
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.DensityCaps

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix Module Function
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p:Shape} {n N:ℕ}

def onePairEquiv (p:Shape) (n N:ℕ):
    (OneOrient p n N×OneOrient p n N)≃OneUnit p n N where
  toFun x i:=if i then x.1 else x.2
  invFun x:=(x true,x false)
  left_inv x:=by simp
  right_inv x:=by funext i; cases i <;> rfl

theorem one_pair_raw (m:Mixer p n):
    mapW (pairW (oneRaw m N) (oneRaw m N)) (onePairEquiv p n N)=oneUnitRaw m N := by
  funext x
  rw [mapW_equiv_val]
  simp only [oneUnitRaw,prodW,Fintype.prod_bool,pairW,onePairEquiv]
  rfl

theorem one_pair_nascent (b:PreparationParameters) (m:Mixer p n)
    (w:Wgt (OneOrient p n N×OneOrient p n N)) (hw:IsLaw w)
    (hcap:pairCaps (oneRaw m N) b.L (bp ((b.D:ℝ)*(2*N))) w):
    OneNascent b m (mapW w (onePairEquiv p n N)) := by
  refine ⟨mapW_law hw _,?_,?_⟩
  · intro i o
    have he:=mapW_nested w (onePairEquiv p n N) (fun x=>x i)
    change mapW (mapW w (onePairEquiv p n N)) (fun x=>x i) o≤_
    rw [he]
    cases i
    · exact hcap.2.1 o
    · exact hcap.1 o
  intro x
  have hh:=mapW_cap hcap.2.2 (onePairEquiv p n N) x
  rw [one_pair_raw] at hh
  exact hh

theorem one_pair_conflict (m:Mixer p n) (w:Wgt (OneOrient p n N×OneOrient p n N)):
    pr (pairW (mapW w (onePairEquiv p n N)) (mapW w (onePairEquiv p n N))) (oneClash m)=
      pr (pairW w w) (fun x=>(oneRawHoles m).conflict x.1 x.2) := by
  rw [←map_pair_law w w (onePairEquiv p n N) (onePairEquiv p n N),mapW_pr]
  rfl

theorem one_pair_card (p:Shape) (n N:ℕ):
    (Fintype.card (OneOrient p n N×OneOrient p n N):ℝ)=
      bp (4*num (Comp p.g)*(dim (OneFull p n):ℝ)*N) := by
  rw [card_space]
  have hd:dim (OneOrient p n N×OneOrient p n N)=
      4*Fintype.card (Comp p.g)*dim (OneFull p n)*N := by
    simp only [dim,OneOrient,OneFrame,OneFull,Module.finrank_prod,
      Module.finrank_pi_fintype,Module.finrank_linearMap,Vec,Module.finrank_self,
      Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_one,HyperbolicIdx,
      Fintype.card_sum,Fintype.card_fin]
    ring
  rw [hd]
  congr 1
  unfold num
  push_cast
  ring

end
end Lax793645Proofs.Simplifications
