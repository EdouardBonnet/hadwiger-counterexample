import Lax793645Proofs.Simplifications.OneSidedOverlap

/-! Nonnegative tests on partition cells bound the positive part of the projected excess. -/

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Function LinearMap Finset Filter
open scoped Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

theorem projected_excess_test_bound {A B : Type} [Fintype A] [Fintype B]
    (ν : Wgt A) (hν : IsLaw ν) (P : A→B) (f p : Wgt A) (hps : lsupp p ν)
    (ε : ℝ) (htest : ∀ φ : Wgt B,(∀ x,0≤φ x ∧ φ x≤1)→
      avg (fun x=>ν x*f x) (φ ∘ P)-avg p (φ ∘ P)≤ε) :
    avg ν (fun x=>max (banner ν P f x-banner ν P (density ν p) x) 0)≤ε := by
  let φ (c : B):=ind (0<cashbook ν P f c-cashbook ν P (density ν p) c)
  have hφ c : 0≤φ c ∧ φ c≤1:=⟨ind_nonneg _,ind_le_one _⟩
  have he x : max (banner ν P f x-banner ν P (density ν p) x) 0=
      (banner ν P f x-banner ν P (density ν p) x)*φ (P x) := by
    dsimp only [φ,banner,Function.comp_apply]
    by_cases hx : 0<cashbook ν P f (P x)-cashbook ν P (density ν p) (P x)
    · rw [ind_one hx,mul_one,max_eq_left hx.le]
    · rw [ind_zero hx,mul_zero,max_eq_right (not_lt.mp hx)]
  have hp : dip ν (density ν p) (φ ∘ P)=avg p (φ ∘ P) := by
    unfold dip avg
    apply sum_congr rfl
    intro x _
    rw [←mul_assoc,←congrFun (dresso ν p hps) x]
  have hf : dip ν f (φ ∘ P)=avg (fun x=>ν x*f x) (φ ∘ P) := by
    unfold dip avg
    apply sum_congr rfl
    intro x _
    ring
  have hh:=htest φ hφ
  calc
    _ = dip ν (banner ν P f) (φ ∘ P)-dip ν (banner ν P (density ν p)) (φ ∘ P) := by
      simp_rw [he,sub_mul]
      rw [avg_sub]
      rfl
    _ = avg (fun x=>ν x*f x) (φ ∘ P)-avg p (φ ∘ P) := by
      rw [cash_orth ν hν.nz,cash_orth ν hν.nz,hp,hf]
    _ ≤ ε := hh

end
end Lax793645Proofs.Simplifications
