import Lax793645Proofs.Simplifications.DependentFrameImages
import Lax793645Proofs.Simplifications.GramPatternSum

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function LinearMap
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I G : Type} [Fintype I] [DecidableEq I] [Fintype G] [DecidableEq G] {N : ℕ}

/-- Uniform probability on a finite dependent product. -/
theorem uniform_product_law {A : G→Type} [∀ i,Fintype (A i)] :
    (unif : Wgt (∀ i,A i))=prodW (fun _=>unif) := by
  have hh:=uniform_pi_event (fun i (_ : A i)=>True)
  simp only [forall_true_iff,unifOn_true] at hh
  exact hh

/-- Independent component probability, in the original global rack. -/
theorem uniform_network_probability (g : Route I G) (p : ∀ i,Rack (Port g i) N→Prop) :
    pr unif (fun x=>∀ i,p i (rackEquiv g N x i))=∏ i,pr unif (p i) := by
  have hh:=mapW_pr unif (rackEquiv g N) (fun x=>∀ i,p i (x i))
  rw [unif_equiv,uniform_product_law,prodW_pr] at hh
  exact hh.symm

variable (g : Route I G) {H : G→Type} [∀ i,Fintype (H i)] [∀ i,DecidableEq (H i)]

def exactNetworkPart (L : ∀ i,Mat (H i) (Port g i)) (Q : ∀ i,Mat (H i) (H i))
    (x : Rack I N) : Prop :=
  ∀ i,prescribedKernelGram (L i) (L i) (Q i) (rackEquiv g N x i)

/-- Original Gram expansion divided by the exact dependent-frame mass.
Only the total nominal deficiency enters the exponent. -/
theorem network_gram_expansion_cost
    (L : ∀ i,Mat (H i) (Port g i)) (Q : ∀ i,Mat (H i) (H i))
    (hL : ∀ i,Surjective (L i).mulVec)
    (hroom : ∀ i,2*num (H i)-(N:ℝ)≤-1) :
    bp (-netSize g)/pr unif (exactNetworkPart (N:=N) g L Q)≤
      (4:ℝ)^Fintype.card G*bp ((N:ℝ)*∑ i,2*(num (Port g i)-num (H i))) := by
  unfold exactNetworkPart
  rw [uniform_network_probability g (fun i z=>prescribedKernelGram (L i) (L i) (Q i) z)]
  have he : bp (-netSize g)=∏ i,bp (-num (Port g i)*num (Port g i)) := by
    unfold netSize
    rw [←Finset.sum_neg_distrib,bp_sum]
    simp only [neg_mul]
  rw [he,←Finset.prod_div_distrib]
  have hp (i : G) : 0≤bp (-num (Port g i)*num (Port g i))/
      pr unif (prescribedKernelGram (U:=Fin N) (L i) (L i) (Q i)) :=
    div_nonneg (bp_pos _).le (pr_nonneg unif_law.nz)
  have hc i := original_gram_expansion_cost (U:=Fin N) (L i) (L i) (hL i) (hL i) (Q i)
    (by simpa only [num,Fintype.card_fin,←two_mul] using hroom i)
  simp only [←pair_unif] at hc
  refine (Finset.prod_le_prod (fun i _=>hp i) (fun i _=>hc i)).trans_eq ?_
  rw [Finset.prod_mul_distrib,Finset.prod_const,card_univ,←bp_sum]
  congr 1
  rw [Finset.mul_sum]
  apply congrArg bp
  apply Finset.sum_congr rfl
  intro i _
  simp only [num,Fintype.card_fin]
  ring

/-- Positivity of the full exact-kernel conditioning event. -/
theorem network_exact_mass_pos
    (L : ∀ i,Mat (H i) (Port g i)) (Q : ∀ i,Mat (H i) (H i))
    (hL : ∀ i,Surjective (L i).mulVec)
    (hroom : ∀ i,2*num (H i)-(N:ℝ)≤-1) :
    0<pr unif (exactNetworkPart (N:=N) g L Q) := by
  unfold exactNetworkPart
  rw [uniform_network_probability g (fun i z=>prescribedKernelGram (L i) (L i) (Q i) z)]
  apply Finset.prod_pos
  intro i _
  have hh:=prescribed_kernel_gram_lower (U:=Fin N) (L i) (L i) (hL i) (hL i) (Q i)
    (by simpa only [num,Fintype.card_fin,←two_mul] using hroom i)
  rw [←pair_unif] at hh
  exact (div_pos (bp_pos _) (by norm_num)).trans_le hh

end
end Lax793645Proofs.Simplifications
