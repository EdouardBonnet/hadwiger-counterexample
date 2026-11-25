import Lax793645Proofs.Simplifications.QuadraticFullCodes
import Mathlib.Data.Sym.Card

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Module Function Finset
open scoped Classical BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I : Type} [Fintype I] [DecidableEq I]

def symmetricPairRead : symmetricRail (univ : Rail I)→ₗ[F]Vec (Sym2 I) where
  toFun M:=Sym2.lift ⟨M.val,fun i j=>(congrFun (congrFun M.property.1 j) i)⟩
  map_add' M L:=by funext z; induction z using Sym2.ind; rfl
  map_smul' c M:=by funext z; induction z using Sym2.ind; rfl

theorem symmetric_pair_read_injective : Injective (symmetricPairRead (I:=I)) := by
  intro M L h
  apply Subtype.ext
  ext i j
  exact congrFun h (Sym2.mk i j)

/-- A quadratic Gram prescription has only the diagonal and one entry
per unordered pair. This sharper count is needed when conditioning the
binary rank estimate on a quadratic frame. -/
theorem quadratic_code_dimension_half :
    2*dim (QuadraticGramCode I)≤Fintype.card I*(Fintype.card I+1) := by
  have h:=LinearMap.finrank_le_finrank_of_injective (symmetric_pair_read_injective (I:=I))
  change dim (symmetricRail (univ : Rail I))≤dim (Vec (Sym2 I)) at h
  rw [dim_vec,Sym2.card,Nat.choose_two_right,Nat.add_sub_cancel,
    quadratic_full_dimension] at h
  rw [Nat.mul_comm (Fintype.card I+1)] at h
  have hd:=Nat.mul_div_le (Fintype.card I*(Fintype.card I+1)) 2
  nlinarith

theorem quadratic_code_dimension_real :
    (dim (QuadraticGramCode I):ℝ)≤(num I*(num I+1))/2 := by
  have h : (2:ℝ)*dim (QuadraticGramCode I)≤num I*(num I+1) := by
    exact_mod_cast quadratic_code_dimension_half (I:=I)
  linarith

end
end Lax793645Proofs.Simplifications
