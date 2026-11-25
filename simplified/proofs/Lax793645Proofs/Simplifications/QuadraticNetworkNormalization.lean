import Lax793645Proofs.Simplifications.QuadraticKernelNormalization
import Lax793645Proofs.Simplifications.QuadraticNetworkTrace
import Lax793645Proofs.Simplifications.NetworkKernelNormalization

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function LinearMap
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I G : Type} [Fintype I] [DecidableEq I] [Fintype G] [DecidableEq G] {N : ℕ}
variable (g : Route I G) {H : G → Type} [∀ i,Fintype (H i)] [∀ i,DecidableEq (H i)]

def quadraticExactNetwork (L : ∀ i,Mat (H i) (Port g i)) (Q : ∀ i,Mat (H i) (H i))
    (x : Rack I N) : Prop:=∀ i,quadraticPrescribedKernel (L i) (Q i) (rackEquiv g N x i)

/-- All original quadratic Gram equations are expanded. The sole
exponential normalization cost is the nominal column deficiency. -/
theorem quadratic_network_expansion_cost
    (L : ∀ i,Mat (H i) (Port g i)) (Q : ∀ i,Mat (H i) (H i))
    (hL : ∀ i,Surjective (L i).mulVec) (hN : ∀ i,2*num (H i)+2 ≤ N) :
    bp (-(dim (symmetricRail (crowded g)):ℝ))/pr unif (quadraticExactNetwork (N:=N) g L Q) ≤
      (4:ℝ)^Fintype.card G*bp (2*(N:ℝ)*∑ i,(num (Port g i)-num (H i))) := by
  unfold quadraticExactNetwork
  rw [uniform_network_probability g (fun i z=>quadraticPrescribedKernel (L i) (Q i) z)]
  have he : bp (-(dim (symmetricRail (crowded g)):ℝ))=
      ∏ i,bp (-(dim (QuadraticGramCode (Port g i)):ℝ)) := by
    rw [quadratic_network_dimension,Nat.cast_sum,←Finset.sum_neg_distrib,bp_sum]
  rw [he,←Finset.prod_div_distrib]
  have hp (i : G) : 0 ≤ bp (-(dim (QuadraticGramCode (Port g i)):ℝ))/
      pr unif (quadraticPrescribedKernel (N:=N) (L i) (Q i)) :=
    div_nonneg (bp_pos _).le (pr_nonneg unif_law.nz)
  have hc i:=quadratic_original_expansion_cost (N:=N) (L i) (hL i) (Q i) (hN i)
  simp only [←pair_unif] at hc
  refine (Finset.prod_le_prod (fun i _=>hp i) (fun i _=>hc i)).trans_eq ?_
  rw [Finset.prod_mul_distrib,Finset.prod_const,card_univ,←bp_sum,←Finset.mul_sum]

theorem quadratic_network_exact_pos
    (L : ∀ i,Mat (H i) (Port g i)) (Q : ∀ i,Mat (H i) (H i))
    (hL : ∀ i,Surjective (L i).mulVec) (hN : ∀ i,2*num (H i)+2 ≤ N) :
    0 < pr unif (quadraticExactNetwork (N:=N) g L Q) := by
  unfold quadraticExactNetwork
  rw [uniform_network_probability g (fun i z=>quadraticPrescribedKernel (L i) (Q i) z)]
  apply Finset.prod_pos
  intro i _
  have hh:=quadratic_prescribed_pos (N:=N) (L i) (hL i) (Q i) (hN i)
  rwa [←pair_unif] at hh

end
end Lax793645Proofs.Simplifications
