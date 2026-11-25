import Lax793645Proofs.Simplifications.ReducedMixers
import Lax793645Proofs.Simplifications.ExplicitMixers

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n : ℕ}

def reducedMixerCount (p : Shape):=Fintype.card (ReducedOne p)
def reducedMixerIndex (p : Shape):ReducedOne p ≃ Fin (reducedMixerCount p):=Fintype.equivFin _

def explicitReduced (d : ReducedDraw p n) : ReducedDraw p n:=
  (fun i=>sharpOverwrite (d.1 i) (explicitShift n (reducedMixerIndex p (i,true)).val),
   (fun i=>sharpOverwrite (d.2.1 i) (explicitShift n (reducedMixerIndex p (i,false)).val)),
   fun ρ=>explicitShift n (reducedMixerCount p+ρ.val))

theorem explicitReduced_sameZ (d : ReducedDraw p n) :
    sameZMixers (reducedMixer d) (reducedMixer (explicitReduced d)) := by
  constructor
  · intro j e f u v huv
    exact congrArg (fun a : F=>cycleWeight e f*a)
      (sharpOverwrite_preserves_Z (d.1 (j,e))
        (explicitShift n (reducedMixerIndex p ((j,e),true)).val) u v huv)
  intro j e f
  exact sharpOverwrite_preserves_Z _ _

theorem explicitReduced_unary (d : ReducedDraw p n) (K s0 : ℕ)
    (h : unaryGood (reducedMixer d) K s0) :
    unaryGood (reducedMixer (explicitReduced d)) K s0 :=
  unaryGood_preserved _ _ (explicitReduced_sameZ d) K s0 h

theorem pull_ordered_reduced (m : ReducedDraw p n) (hg : 3≤p.g) (s t : Label p.b) (i : ReducedOne p) :
    pullM (blockRay p n s Block.sharp) (blockRay p n t Block.sharp)
      (reducedOrdered (reducedMixer (explicitReduced m)) i) = explicitShift n (reducedMixerIndex p i).val := by
  rw [reduced_ordered_drawn hg]
  rcases i with ⟨i,b⟩
  cases b <;> simp [explicitReduced,pull_sharpOverwrite]

theorem pull_either_reduced (m : ReducedDraw p n) (hg : 3≤p.g) (s t : Label p.b) (i : ReducedOne p) (b : Bool) :
    pullM (blockRay p n s Block.sharp) (blockRay p n t Block.sharp)
      (eitherM b (reducedOrdered (reducedMixer (explicitReduced m)) i)) =
      eitherM b (explicitShift n (reducedMixerIndex p i).val) := by
  cases b <;> simp [eitherM,pull_transpose_pair,pull_ordered_reduced m hg]

theorem pull_self_reduced (m : ReducedDraw p n) (hg : 3≤p.g) (s t : Label p.b) (hj : 1 ≤ p.j) (b : Bool) :
    pullM (blockRay p n s Block.sharp) (blockRay p n t Block.sharp)
      (eitherM b (selfM p n (reducedMixer (explicitReduced m)).mixM)) =
      eitherM b (∑ ρ, (s ρ+t ρ) • explicitShift n (reducedMixerCount p+ρ.val)) := by
  cases b
  · simp only [eitherM, Bool.false_eq_true, if_false, pull_transpose_pair,
      pull_self_sharp _ _ _ hj, reducedMixer,explicitReduced]
    simp_rw [add_comm (t _)]
  · simp [eitherM,pull_self_sharp _ _ _ hj,reducedMixer,explicitReduced]

def reducedParityCoefficients (p : Shape) (c : Vec (ReducedBits p)) (b : Vec Bool)
    (s t : Label p.b) (v : Bool) : Fin (reducedMixerCount p+p.b) → F :=
  mixerCoefficients (fun k => c ((reducedMixerIndex p).symm k,v)) (b v) s t

theorem reducedParityCoefficients_sum (c : Vec (ReducedBits p)) (b : Vec Bool)
    (s t : Label p.b) (v : Bool) :
    (∑ k, reducedParityCoefficients p c b s t v k • explicitShift n k.val) =
    (∑ i : ReducedOne p, c (i,v) • explicitShift n (reducedMixerIndex p i).val) +
      b v • (∑ ρ, (s ρ+t ρ) • explicitShift n (reducedMixerCount p+ρ.val)) := by
  rw [Fin.sum_univ_add]
  simp only [reducedParityCoefficients,mixerCoefficients,Fin.addCases_left,Fin.addCases_right,
    Fin.val_castAdd,Fin.val_natAdd,Finset.smul_sum,smul_smul]
  congr 1
  simpa only [Equiv.symm_apply_apply] using (Equiv.sum_comp (reducedMixerIndex p) (fun k =>
    c ((reducedMixerIndex p).symm k,v) • explicitShift n k.val)).symm

theorem pull_parity_reduced (m : ReducedDraw p n) (hg : 3≤p.g) (s t : Label p.b) (hj : 1 ≤ p.j)
    (c : Vec (ReducedBits p)) (b : Vec Bool) :
    pullM (blockRay p n s Block.sharp) (blockRay p n t Block.sharp)
      (reducedIndexedSum (reducedMixer (explicitReduced m)) c+selfSum (reducedMixer (explicitReduced m)) b) =
      (∑ k, reducedParityCoefficients p c b s t true k • explicitShift n k.val) +
      (∑ k, reducedParityCoefficients p c b s t false k • (explicitShift n k.val).transpose) := by
  simp only [reducedIndexedSum,selfSum,map_add,map_sum,map_smul,pull_either_reduced m hg,
    pull_self_reduced m hg s t hj]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool,eitherM,Bool.false_eq_true,if_false,if_true,
    Finset.sum_add_distrib]
  have ht := reducedParityCoefficients_sum (n:=n) c b s t true
  have hf := congrArg Matrix.transpose (reducedParityCoefficients_sum (n:=n) c b s t false)
  simp only [Matrix.transpose_sum,Matrix.transpose_smul,Matrix.transpose_add] at hf
  rw [ht,hf]
  simp only [Matrix.transpose_sum,Matrix.transpose_smul]
  exact add_add_add_comm (G:=Mat (Fin n) (Fin n)) _ _ _ _

theorem reducedParityCoefficients_nonzero (c : Vec (ReducedBits p)) (b : Vec Bool)
    (s t : Label p.b) (hst : s ≠ t) (h : c ≠ 0 ∨ b ≠ 0) :
    reducedParityCoefficients p c b s t true ≠ 0 ∨ reducedParityCoefficients p c b s t false ≠ 0 := by
  classical
  have hbase : (fun k => c ((reducedMixerIndex p).symm k,true)) ≠ 0 ∨
      (fun k => c ((reducedMixerIndex p).symm k,false)) ≠ 0 ∨ b true ≠ 0 ∨ b false ≠ 0 := by
    by_contra! hz
    rcases h with hc | hb
    · apply hc
      funext i
      rcases i with ⟨i,v⟩
      cases v
      · simpa using congr_fun hz.2.1 (reducedMixerIndex p i)
      · simpa using congr_fun hz.1 (reducedMixerIndex p i)
    · apply hb
      funext v
      cases v
      · exact hz.2.2.2
      · exact hz.2.2.1
  rcases hbase with h1 | h2 | h3 | h4
  · exact Or.inl (mixerCoefficients_nonzero _ _ s t hst (Or.inl h1))
  · exact Or.inr (mixerCoefficients_nonzero _ _ s t hst (Or.inl h2))
  · exact Or.inl (mixerCoefficients_nonzero _ _ s t hst (Or.inr h3))
  · exact Or.inr (mixerCoefficients_nonzero _ _ s t hst (Or.inr h4))

theorem explicitReduced_binary_rank (m : ReducedDraw p n) (hg : 3≤p.g) (hj : 1 ≤ p.j)
    (hn : 4*(reducedMixerCount p+p.b)+4 ≤ n) (s t : Label p.b) (hst : s ≠ t)
    (c : Vec (ReducedBits p)) (b : Vec Bool) (h : c ≠ 0 ∨ b ≠ 0) :
    n ≤ 5*blockRank Block.sharp s t (reducedIndexedSum (reducedMixer (explicitReduced m)) c+selfSum (reducedMixer (explicitReduced m)) b) := by
  unfold blockRank
  rw [pull_parity_reduced m hg s t hj]
  have hr := explicitShift_rank (n:=n) _ _ (reducedParityCoefficients_nonzero c b s t hst h)
  have hmargin := shift_rank_fifth hn
  omega

end
end Lax793645Proofs.Simplifications
