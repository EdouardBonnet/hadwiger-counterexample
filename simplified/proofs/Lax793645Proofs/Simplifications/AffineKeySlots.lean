/-
Adapted from the corresponding finite key-rank calculation in
ConditionalCellEntropy (OpenAI, fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb,
Apache-2.0). Protection is supplied by the new tensor argument.
-/
import Lax793645Proofs.Simplifications.AffineKeyDirections
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.ConditionalCellEntropy

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Submodule Module Finset
open scoped BigOperators
noncomputable section
variable {p : Shape} {n : ℕ} {I : Type} [Fintype I]

theorem affine_key_slots (v : Volley p n I) (t : Tagging p I) {q} {a : Plan p n}
    (h : affineAvoids v a q) :
    planNew a (v.keyPlan t) = kslots p I := by
  classical
  let Y := Volley.visits p t
  have hh i := affine_key_independent v t a q h i
  have he (z : Place p) : dim (v.keyPlan t z)=Fintype.card (Y z.1) :=
    mrk_inj.mp (hh z).1
  rw [plan_new_disjoint a _ (fun i => Disjoint.mono_left (pin_le_table a i)
    (hh i).2.symm), planRank,Fintype.sum_prod_type]
  simp_rw [Fintype.sum_bool,he,←two_mul,←Finset.mul_sum]
  have hE : ∑ i : Comp p.g,Fintype.card (Y i)=Fintype.card I*(tagDegree p.g) := by
    have hf {A : Type} [Fintype A] (p : A → Prop) [DecidablePred p] :
        Fintype.card {i:A//p i}=∑ i:A, if p i then (1:ℕ) else 0 := by
      rw [Fintype.card_subtype,←Finset.sum_filter]; simp

    have hY (i) : Fintype.card (Y i)=∑ j:I,if inc i (t j) then (1:ℕ) else 0 := hf _
    simp_rw [hY]
    rw [Finset.sum_comm]
    simp_rw [← hf (fun i => inc i _)]
    have hz (j) : Fintype.card {i:Comp p.g//inc i (t j)}=tagDegree p.g := card_star (t j)
    simp_rw [hz]
    simp
  rw [hE]; unfold kslots; ring

end
end Lax793645Proofs.Simplifications
