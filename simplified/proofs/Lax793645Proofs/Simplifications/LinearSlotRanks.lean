import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.FiniteAffineLaws
import Mathlib.LinearAlgebra.Dimension.Free

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open LinearMap Module Function Finset
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {E D V W : Type} [Fintype E]
  [AddCommGroup D] [Module F D] [FiniteDimensional F D]
  [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  [AddCommGroup W] [Module F W] [FiniteDimensional F W]

theorem linear_slot_dimension (T : D→ₗ[F](E→V)) (hT : Injective T) :
    dim D≤∑ e,dim (((LinearMap.proj e).comp T).range) := by
  let A (e : E):=(LinearMap.proj e).comp T
  let L : D→ₗ[F](∀ e, (A e).range):=LinearMap.pi (fun e=>(A e).rangeRestrict)
  have hL : Injective L := by
    intro x y h
    apply hT
    funext e
    exact congrArg Subtype.val (congrFun h e)
  have hd:=LinearMap.finrank_le_finrank_of_injective hL
  simpa only [Module.finrank_pi_fintype,dim,A] using hd

theorem linear_slot_large_rank [Nonempty E] (T : D→ₗ[F](E→V)) (hT : Injective T)
    (d : ℕ) (hd : Fintype.card E*d≤dim D) :
    ∃ e,d≤dim (((LinearMap.proj e).comp T).range) := by
  have hs : (∑ _e : E,d)≤∑ e,dim (((LinearMap.proj e).comp T).range) := by
    simpa only [sum_const,card_univ,smul_eq_mul] using hd.trans (linear_slot_dimension T hT)
  obtain ⟨e,_,he⟩:=Finset.exists_le_of_sum_le (Finset.univ_nonempty) hs
  exact ⟨e,he⟩

/-- A map of rank at least d contains an injective d-dimensional restriction. -/
theorem linear_rank_restriction (T : D→ₗ[F]V) (d : ℕ) (hd : d≤dim T.range) :
    ∃ J : Vec (Fin d)→ₗ[F]D,Injective (T.comp J) := by
  have hdim : finrank F (Vec (Fin d))≤finrank F T.range:=by
    simpa only [dim_vec,Fintype.card_fin] using hd
  obtain ⟨A,hA⟩:=finrank_le_iff_exists_linearMap.mp hdim
  obtain ⟨s,hs⟩:=T.rangeRestrict.exists_rightInverse_of_surjective
    (range_eq_top.mpr T.surjective_rangeRestrict)
  refine ⟨s.comp A,?_⟩
  intro x y hxy
  apply hA
  have he : ∀ z, T.rangeRestrict (s (A z))=A z:=fun z=>by
    exact LinearMap.congr_fun hs (A z)
  rw [←he x,←he y]
  apply Subtype.ext
  exact hxy

end
end Lax793645Proofs.Simplifications
