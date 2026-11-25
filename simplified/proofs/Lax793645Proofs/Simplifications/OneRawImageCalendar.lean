import Lax793645Proofs.Simplifications.OneInjectionCalendar
import Lax793645Proofs.Simplifications.OneDualImages

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Module Submodule Filter
open scoped BigOperators Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- All raw image and room estimates are produced after fixing the
quadratic construction constants; the ambient scale is chosen last. -/
theorem one_raw_image_calendar (p : Shape) {ζ : ℝ} (hz : 0<ζ) (hz' : ζ≤6) :
    ∀ᶠ M : ℕ in atTop,∀ᶠ n : ℕ in atTop,let N:=M*n;
      Fintype.card (Row p n)+2*p.h+1≤N ∧5≤N ∧4*p.h+3≤N ∧
      ∀ (m : Mixer p n) (a : ImagePin (Comp p.g) (OneColumn p n) (2*N)),
        pr (oneUnitRaw m N) (imagePinAgree oneDualImages a)≤fee (2*N) ζ (imagePlanRank a.sp) := by
  have hz6 : 0<ζ/3:=by positivity
  filter_upwards [columns_budget p (δ:=1) zero_lt_one 4 5 (by norm_num) (by norm_num),
    columns_budget p (δ:=ζ/3) hz6 4 5 (by norm_num) (by norm_num)] with M hA hB
  filter_upwards [eventually_ge_atTop 1] with n hn
  dsimp only
  let N:=M*n
  have hA:=hA n hn
  have hB:=hB n hn
  rw [one_mul] at hA
  have hfull : num (Full p n)=num (Row p n)+p.h := by simp [num,Full,Chan]
  rw [hfull] at hA hB
  have hrow : 0≤num (Row p n):=Nat.cast_nonneg _
  have hh : 0≤(p.h:ℝ):=Nat.cast_nonneg _
  have hroom : Fintype.card (Row p n)+2*p.h+1≤N := by
    have h : num (Row p n)+2*p.h+1≤N:=by linarith
    exact_mod_cast h
  have h5 : 5≤N := by
    have h : (5:ℝ)≤N:=by linarith
    exact_mod_cast h
  have h4 : 4*p.h+3≤N := by
    have h : 4*(p.h:ℝ)+3≤N:=by linarith
    exact_mod_cast h
  have hN : 2*dim (OneFull p n)+3≤N := by
    rw [one_full_dimension]
    have h : 2*(num (Row p n)+2*p.h)+3≤N:=by linarith
    exact_mod_cast h
  have hζ : (dim (OneFull p n):ℝ)+2≤(ζ/6)*(2*N) := by
    rw [one_full_dimension]
    push_cast
    change num (Row p n)+2*p.h+2≤_
    linarith
  exact ⟨hroom,h5,h4,fun m a=>one_dual_image_pin_cap m a hz.le hz' hN hζ⟩

end
end Lax793645Proofs.Simplifications
