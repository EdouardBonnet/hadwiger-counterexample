import Lax793645Proofs.Simplifications.OneLinearKeyPalette
import Lax793645Proofs.Simplifications.OneSurrogateProductBounds

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis Filter Finset Matrix Function
open scoped Classical BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N r R : ℕ} {q : Format} {d : Rates} {b : Bool}
namespace OneQuill
variable (w : Quill p q d b) (t : Tagging p (Messenger q)) (z : Messenger q→F)
  (o : OneUnit p n N) (m : Mixer p n) (s : Charts p n d) (Y : OneSilhouette p N r)

theorem one_prowl_linear_sum {I : Type} [Fintype I]
    (c : Wgt I) (W : I→Wgt (OneKeys t N)) :
    oneProwl w t z o m s (fun x=>∑ i,c i*W i x)=
      ∑ i,c i*oneProwl w t z o m s (W i) := by
  unfold oneProwl
  simp only [Finset.sum_mul,avg_sum,mul_assoc,avg_mul']

theorem one_sheen_linear_sum {I : Type} [Fintype I]
    (c : Wgt I) (W : I→Wgt (OneKeys t N)) :
    oneSheen w t z o m s Y (fun x=>∑ i,c i*W i x)=
      ∑ i,c i*oneSheen w t z o m s Y (W i) := by
  unfold oneSheen
  simp only [Finset.mul_sum,avg_sum]
  apply sum_congr rfl
  intro i _
  rw [←avg_mul']
  exact avg_congr (fun x _=>by ring)

/-- Exact product expansion transfers the unary-table comparison to
every bounded test of a whole linear key partition. -/
theorem one_linear_query_test (L : OneKeys t N→ₗ[F]Vec (Fin R))
    (hY : OneRefines Y (oneLinearKeyPalette t L))
    (φ : Wgt (Vec (Fin R))) (hφ : ∀ x,|φ x|≤1)
    (hκ : ∀ i,IsLaw (w.policies t z n i)) (hframe : ∀ i,oneFrameLaw m (o i))
    (hj : 1≤p.j) (hm : reducedBinaryGood m) (hfire : oneLitFire o) (hsel : (w.pen t).diffsel)
    (C : ℝ) (hC : 0<C) (hcap : ∀ i x,w.policies t z n i x≤C*unif x)
    {ε : ℝ} (hclose : ∀ i,OneAppearance.oneClose (w.allure t z i) Y (o (parcel b i)) ε)
    (hN : 2*num ((Messenger q)×Toast p)+2≤(N:ℝ)) :
    |oneProwl w t z o m s (φ ∘ L)-oneSheen w t z o m s Y (φ ∘ L)|≤
      num (Messenger q→Vec (Fin R))*(C^2*bp (-(n:ℝ)/10)+num (Messenger q)*ε+
        2*quadraticNetFact (trayPort p t)*bp (-(N:ℝ)/2)) := by
  obtain ⟨U,hU,hdecomp⟩:=one_linear_cell_expansion t z L Y hY
  have hf : φ ∘ L=fun x=>∑ a : Messenger q→Vec (Fin R),
      φ (∑ i,a i)*prodW (oneCellTest t z Y (U a)) x := funext (hdecomp φ)
  rw [hf,one_prowl_linear_sum,one_sheen_linear_sum,←sum_sub_distrib]
  apply (abs_sum_le_sum_abs ..).trans
  calc
    _ ≤ ∑ a : Messenger q→Vec (Fin R),
        (C^2*bp (-(n:ℝ)/10)+num (Messenger q)*ε+
        2*quadraticNetFact (trayPort p t)*bp (-(N:ℝ)/2)) := by
      apply sum_le_sum
      intro a _
      rw [←mul_sub,abs_mul]
      exact ((mul_le_mul_of_nonneg_right (hφ _) (abs_nonneg _)).trans_eq (one_mul _)).trans
        (one_cell_query_comparison w t z o m s Y (U a) (hU a) hκ hframe hj hm hfire hsel
          C hC hcap hclose hN)
    _ = _ := by simp only [sum_const,card_univ,nsmul_eq_mul,num]

end OneQuill
end
end Lax793645Proofs.Simplifications
