import Lax793645Proofs.Simplifications.OneAnalyticParameters

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Filter Matrix
open scoped Topology
noncomputable section

theorem one_collision_calendar (p:Shape) (K:ℕ):
    ∀ᶠ M:ℕ in atTop,∀ᶠ n:ℕ in atTop,let N:=M*n;
      100≤2*N ∧ (dim (OneCheckGram p n):ℝ)≤0.01*(2*N) ∧
      (K+(oneMaxSlots p:ℝ))*num (OneColumn p n)≤0.005*(2*N) := by
  filter_upwards [columns_budget p (δ:=0.01) (by norm_num)
    (16*(num (Comp p.g))*p.h) 0 (by positivity) (by norm_num),
    columns_budget p (δ:=0.005) (by norm_num)
      (4*(K+(oneMaxSlots p:ℝ))) 0 (by positivity) (by norm_num),
    eventually_ge_atTop 1] with M hA hB hM
  filter_upwards [eventually_ge_atTop 100] with n hn
  have hA:=hA n (by omega)
  have hB:=hB n (by omega)
  have hN:100≤M*n:=by nlinarith only [hM,hn]
  have hfull:num (Full p n)=num (Row p n)+p.h:=by simp [num,Full]
  rw [add_zero,hfull] at hA hB
  refine ⟨by omega,?_,?_⟩
  · rw [one_channel_test_dimension]
    push_cast
    change 16*num (Comp p.g)*p.h*num (Row p n)≤_
    have hle:16*num (Comp p.g)*p.h*num (Row p n)≤
        16*num (Comp p.g)*p.h*(num (Row p n)+p.h):=
      mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (Nat.cast_nonneg _)) (by positivity)
    push_cast at hA
    nlinarith only [hle,hA,mul_nonneg (Nat.cast_nonneg (α:=ℝ) M) (Nat.cast_nonneg (α:=ℝ) n)]
  rw [one_column_size]
  have hrow:0≤num (Row p n):=by unfold num; positivity
  have hpos:0≤(K:ℝ)+oneMaxSlots p:=by positivity
  nlinarith only [hB,mul_nonneg hpos hrow,Nat.cast_nonneg (α:=ℝ) (M*n)]

end
end Lax793645Proofs.Simplifications
