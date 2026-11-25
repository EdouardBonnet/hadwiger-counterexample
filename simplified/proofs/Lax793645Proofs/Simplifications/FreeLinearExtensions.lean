import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.FiniteAffineLaws
import Mathlib.LinearAlgebra.Dual.Lemmas

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open LinearMap Module
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {B C V : Type} [AddCommGroup B] [Module F B] [AddCommGroup C] [Module F C]
  [AddCommGroup V] [Module F V] [FiniteDimensional F B] [FiniteDimensional F C]
  [FiniteDimensional F V] [Fintype B] [Fintype C] [Fintype V] [Fintype (C→ₗ[F]V)]

/-- A random linear map sends each fixed nonzero vector uniformly. -/
theorem free_linear_evaluation (c : C) (hc : c≠0) (v : V) :
    pr unif (fun L : C→ₗ[F]V=>L c=v)=bp (-(dim V:ℝ)) := by
  let E : (C→ₗ[F]V)→ₗ[F]V:={
    toFun L:=L c
    map_add' _ _:=rfl
    map_smul' _ _:=rfl }
  obtain ⟨φ,hφ⟩:=Module.Projective.exists_dual_eq_one F hc
  have he : Function.Surjective E:=fun v=>⟨φ.smulRight v,by simp [E,hφ]⟩
  change mapW unif E v=_
  rw [map_unif_surjective E he,unif_apply,card_space,bp_neg]

/-- Adding unconstrained columns to an injection fails only when a
nonzero new combination lands in the old image. -/
theorem free_extension_failure (P : B→ₗ[F]V) (hP : Function.Injective P) :
    pr unif (fun Y : C→ₗ[F]V=>¬Function.Injective (P.coprod Y))≤
      bp ((dim B:ℝ)+dim C-dim V) := by
  classical
  let E (u : B×C) (Y : C→ₗ[F]V):=u.2≠0 ∧ Y u.2=-(P u.1)
  have hw (Y : C→ₗ[F]V) (hy : ¬Function.Injective (P.coprod Y)) : ∃ u,E u Y := by
    have hker : ¬∀ u,(P.coprod Y) u=0→u=0 := by
      intro hh
      apply hy
      intro u v huv
      apply sub_eq_zero.mp
      apply hh
      rw [map_sub,huv,sub_self]
    push Not at hker
    obtain ⟨⟨b,c⟩,he,hn⟩:=hker
    have hc : c≠0 := by
      intro hc
      subst c
      have hb : b=0:=hP (by simpa using he)
      exact hn (by simp [hb])
    refine ⟨(b,c),hc,?_⟩
    change P b+Y c=0 at he
    exact eq_neg_of_add_eq_zero_left (by rw [add_comm];exact he)
  have he (u : B×C) : pr unif (E u)≤bp (-(dim V:ℝ)) := by
    by_cases hu : u.2=0
    · simp [E,hu,pr_false,(bp_pos _).le]
    · simp only [E,hu,ne_eq,not_false_eq_true,true_and]
      exact (free_linear_evaluation u.2 hu _).le
  refine ((pr_mono unif_law.nz hw).trans (pr_exists_le unif_law.nz E)).trans ?_
  apply (Finset.sum_le_sum (fun u _=>he u)).trans_eq
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Fintype.card_prod,Nat.cast_mul,
    card_space,←bp_add,sub_eq_add_neg]

end
end Lax793645Proofs.Simplifications
