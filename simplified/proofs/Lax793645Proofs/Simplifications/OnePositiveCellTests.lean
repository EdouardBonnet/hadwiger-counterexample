import Lax793645Proofs.Simplifications.OneLinearKeyPalette

/-! A test on a linear tuple partition is an exact sum of products of nonnegative unary cell tests. -/

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Function LinearMap Finset StatusAnalysis Filter
open scoped Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

section
variable {p : Shape} {N R r : ℕ} {I : Type} [Fintype I] [DecidableEq I]
theorem one_linear_positive_expansion (t : Tagging p I) (z : I→F)
    (L : OneKeys t N→ₗ[F]Vec (Fin R)) (Y : OneSilhouette p N r)
    (hY : OneRefines Y (oneLinearKeyPalette t L)) :
    ∃ U : (I→Vec (Fin R))→I→Fin r→ℝ,(∀ a i c,0≤U a i c ∧ U a i c≤1) ∧
      ∀ (φ : Wgt (Vec (Fin R))) (x : OneKeys t N),
        φ (L x)=∑ a : I→Vec (Fin R),φ (∑ i,a i)*∏ i,U a i (Y (t i) (z i) (x i)) := by
  choose f hf using fun i=>hY (t i) (z i)
  let E:=Fintype.equivFin (I→Vec (Fin R))
  let U (a : I→Vec (Fin R)) (i : I) (c : Fin r):=ind (E.symm (f i c) i=a i)
  refine ⟨U,fun a i c=>⟨ind_nonneg _,ind_le_one _⟩,?_⟩
  intro φ x
  let a (i : I):=L (Pi.single i (x i))
  have he : ∑ i,a i=L x := by
    dsimp only [a]
    rw [←map_sum,Finset.univ_sum_single]
  have hr (i : I) : E.symm (f i (Y (t i) (z i) (x i))) i=a i := by
    rw [←hf i (x i)]
    exact one_linear_key_palette_read t L i (z i) (x i)
  have hh (c : I→Vec (Fin R)) : (∏ i,U c i (Y (t i) (z i) (x i)))=ind (a=c) := by
    simp only [U,hr,←ind_all,←funext_iff]
  simp_rw [hh]
  rw [Finset.sum_eq_single a]
  · rw [ind_one rfl,mul_one,he]
  · intro c _ hc
    rw [ind_zero (Ne.symm hc),mul_zero]
  · simp

end

end
end Lax793645Proofs.Simplifications
