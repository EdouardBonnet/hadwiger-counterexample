import Lax793645Proofs.Simplifications.QuadraticRailSpaces

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function LinearMap Module Submodule
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I : Type} [Fintype I] [DecidableEq I]

theorem quadratic_full_code_eq (G H : Mat I I) :
    quadraticRailRead (univ : Rail I) G=quadraticRailRead univ H ↔
      quadraticGramCode G=quadraticGramCode H := by
  constructor
  · intro h
    apply Subtype.ext
    funext v
    let M : symmetricRail (univ : Rail I):=⟨vecMulVec v v,transpose_vecMulVec v v,
      fun _ _ hn=>(hn (mem_univ _)).elim⟩
    have hh:=LinearMap.congr_fun h M
    rw [quadratic_rail_read_value,quadratic_rail_read_value] at hh
    dsimp only [M] at hh
    rw [mpair_comm (vecMulVec v v) G,mpair_comm (vecMulVec v v) H,
      mpair_outer,mpair_outer] at hh
    exact hh
  · intro h
    apply LinearMap.ext
    intro M
    rw [quadratic_rail_read_value,quadratic_rail_read_value]
    exact symmetric_pairing_quadratic_code M.val G H M.property.1 h

theorem quadratic_full_dimension :
    dim (symmetricRail (univ : Rail I))=dim (QuadraticGramCode I) := by
  have hk : (quadraticRailRead (univ : Rail I)).ker=(quadraticGramCode (I:=I)).ker := by
    ext G
    change quadraticRailRead univ G=0 ↔ quadraticGramCode G=0
    rw [←map_zero (quadraticRailRead (univ : Rail I)),←map_zero (quadraticGramCode (I:=I))]
    exact quadratic_full_code_eq G 0
  have h₁:=(quadraticRailRead (univ : Rail I)).finrank_range_add_finrank_ker
  have h₂:=(quadraticGramCode (I:=I)).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (quadratic_rail_read_surjective univ),finrank_top,
    Subspace.dual_finrank_eq,hk] at h₁
  rw [LinearMap.range_eq_top.mpr quadratic_gram_code_surjective,finrank_top] at h₂
  exact Nat.add_right_cancel (h₁.trans h₂.symm)

end
end Lax793645Proofs.Simplifications
