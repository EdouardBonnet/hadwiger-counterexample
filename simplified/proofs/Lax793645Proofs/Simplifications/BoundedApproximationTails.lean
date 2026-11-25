import Lax793645Proofs.Simplifications.FilteredColoredDensities
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.RestrictedComparisonLaws
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.ProjectionError

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset
open scoped Classical
noncomputable section
variable {X : Type} [Fintype X]

/-- A bounded approximation to one dominating density controls every
submeasure. The clipping height does not depend on the approximation error. -/
theorem dominated_approximation_tails (ν W g : Wgt X)
    (hν : ∀ x,0≤ν x) (hW : lsupp W ν)
    (B ε : ℝ) (hg : ∀ x,g x≤B) (he : lcost ν (density ν W) g≤ε)
    (p : Wgt X) (hp : ∀ x,0≤p x) (hdom : ∀ x,p x≤W x) :
    (∀ S : X→Prop,pr p S≤B*pr ν S+ε) ∧
    pr p (fun x=>2*B≤density ν p x)≤2*ε := by
  have hs : lsupp p ν := by
    intro x hx
    apply hW x
    intro hh
    exact hx (le_antisymm ((hdom x).trans_eq hh) (hp x))
  have hd x : density ν p x≤density ν W x :=
    div_le_div_of_nonneg_right (hdom x) (hν x)
  have hpr (S : X→Prop) :
      pr p S=avg ν (fun x=>density ν p x*ind (S x)) :=
    (supported_density_average ν p hs (fun x=>ind (S x))).symm
  constructor
  · intro S
    rw [hpr]
    calc
      _≤avg ν (fun x=>B*ind (S x)+|density ν W x-g x|) := by
        apply avg_mono hν
        intro x
        by_cases hx : S x
        · rw [ind_one hx,mul_one,mul_one]
          linarith only [hd x,hg x,le_abs_self (density ν W x-g x)]
        · rw [ind_zero hx,mul_zero,mul_zero,zero_add]
          exact abs_nonneg _
      _=B*pr ν S+lcost ν (density ν W) g := by
        rw [avg_add,avg_mul']
        rfl
      _≤B*pr ν S+ε:=add_le_add le_rfl he
  · rw [hpr]
    calc
      _≤avg ν (fun x=>2*|density ν W x-g x|) := by
        apply avg_mono hν
        intro x
        by_cases hx : 2*B≤density ν p x
        · rw [ind_one hx,mul_one]
          linarith only [hx,hd x,hg x,le_abs_self (density ν W x-g x)]
        · rw [ind_zero hx,mul_zero]
          exact mul_nonneg (by norm_num) (abs_nonneg _)
      _=2*lcost ν (density ν W) g := by rw [avg_mul']; rfl
      _≤2*ε:=mul_le_mul_of_nonneg_left he (by norm_num)

end
end Lax793645Proofs.Simplifications
