import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.PolynomialZeroTests

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Submodule Finset
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

theorem linear_coordinate_stocks (A : Vec I→ₗ[F]Vec J) (j : J) :
    (fun x=>A x j)∈Stocks I 1 := by
  have he : (fun x=>A x j)=∑ i : I,LinearMap.toMatrix' A j i • (fun x=>x i) := by
    funext x
    rw [←LinearMap.toMatrix'_mulVec A x]
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Matrix.mulVec,dotProduct]
  rw [he]
  exact Submodule.sum_mem _ fun i _=>Submodule.smul_mem _ _ (stock_var i)

theorem affine_coordinate_stocks (A : Vec I→ₗ[F]Vec J) (b : Vec J) (j : J) :
    (fun x=>(A x+b) j)∈Stocks I 1 :=
  Submodule.add_mem _ (linear_coordinate_stocks A j) (stocks_one I 1 (b j))

theorem monomial_affine_substitution (P : Vec I→Vec J)
    (hP : ∀ j,(fun x=>P x j)∈Stocks I 1) (s : Finset J) :
    (fun x=>poly1 s (P x))∈Stocks I s.card := by
  induction s using Finset.induction_on with
  | empty => simpa only [poly1,Finset.prod_empty,Finset.card_empty] using stocks_one I 0 1
  | @insert j s hj ih =>
    have he : (fun x=>poly1 (insert j s) (P x))=
        (fun x=>P x j)*(fun x=>poly1 s (P x)) := by
      funext x
      simp only [poly1,Finset.prod_insert hj,Pi.mul_apply]
    rw [he,Finset.card_insert_of_notMem hj,Nat.add_comm s.card 1]
    exact stock_prod (hP j) ih

/-- Affine substitution does not increase Boolean polynomial degree. -/
theorem polynomial_affine_substitution (d : ℕ) (f : Vec J→F)
    (hf : f∈Stocks J d) (P : Vec I→Vec J)
    (hP : ∀ j,(fun x=>P x j)∈Stocks I 1) :
    (fun x=>f (P x))∈Stocks I d := by
  unfold Stocks at hf
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨s,hs,rfl⟩ := hf
    exact stocks_rise I hs (monomial_affine_substitution P hP s)
  | zero => exact Submodule.zero_mem _
  | add f g _ _ hf hg => exact Submodule.add_mem _ hf hg
  | smul a f _ hf => exact Submodule.smul_mem _ a hf

theorem monomial_degree_substitution (e : ℕ) (P : Vec I→Vec J)
    (hP : ∀ j,(fun x=>P x j)∈Stocks I e) (s : Finset J) :
    (fun x=>poly1 s (P x))∈Stocks I (s.card*e) := by
  induction s using Finset.induction_on with
  | empty => simpa only [poly1,Finset.prod_empty,Finset.card_empty,Nat.zero_mul]
      using stocks_one I 0 1
  | @insert j s hj ih =>
    have he : (fun x=>poly1 (insert j s) (P x))=
        (fun x=>P x j)*(fun x=>poly1 s (P x)) := by
      funext x
      simp only [poly1,Finset.prod_insert hj,Pi.mul_apply]
    rw [he,Finset.card_insert_of_notMem hj,Nat.add_mul,Nat.one_mul,Nat.add_comm]
    exact stock_prod (d:=e) (j:=s.card*e) (hP j) ih

theorem polynomial_degree_substitution (d e : ℕ) (f : Vec J→F)
    (hf : f∈Stocks J d) (P : Vec I→Vec J)
    (hP : ∀ j,(fun x=>P x j)∈Stocks I e) :
    (fun x=>f (P x))∈Stocks I (d*e) := by
  unfold Stocks at hf
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨s,hs,rfl⟩ := hf
    exact stocks_rise I (Nat.mul_le_mul_right e hs) (monomial_degree_substitution e P hP s)
  | zero => exact Submodule.zero_mem _
  | add f g _ _ hf hg => exact Submodule.add_mem _ hf hg
  | smul a f _ hf => exact Submodule.smul_mem _ a hf

end
end Lax793645Proofs.Simplifications
