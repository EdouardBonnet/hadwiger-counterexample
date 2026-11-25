import Lax793645Proofs.Simplifications.OneTableFlags
import Lax793645Proofs.Simplifications.OneScalarRecipes

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Submodule Module Function Finset
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {p : Shape} {n N : ℕ}

def oneContract (T : OneCross p n) (i j : Bool) : Profile p n→ₗ[F]F:=
  (jointMatrixFunctional (fun e=>channelQuadraticMatrix p.h
    (unitLeftChannels p.h (oneTableOfCross T e) j))).comp (jointEndpointMap i)

theorem one_contract_actual (x y : OneUnit p n N) (i j : Bool)
    (z : Profile p n) (hz : z∈Xspace p n) :
    oneContract (oneCrossMatrix x y) i j z=oneFunctional (y j) (oneMomentEmbed (x i) z) := by
  simpa only [oneContract,LinearMap.comp_apply,one_actual_table] using
    one_actual_channel_contract x y i j z hz

theorem one_fits_channel_values (a b : ImagePlan (Comp p.g) (OneColumn p n))
    (ha : (onePinClosure p n).close a=a) (T Q : OneCross p n) (hf : oneFitsTable a b T Q)
    (e : Comp p.g) (i j : Bool) {v : Ray p n} (hv : v∈oneEndpointPrimalPins a i e) :
    unitLeftChannels p.h (oneTableOfCross T e) j (jointInjection i v)=
      unitLeftChannels p.h (oneTableOfCross Q e) j (jointInjection i v) := by
  apply (LinearMap.BilinForm.toDual (hyperbolicQuadratic p.h).polarBilin
    (hyperbolic_nondegenerate p.h)).injective
  apply LinearMap.ext
  intro c
  change (hyperbolicQuadratic p.h).polarBilin _ c=(hyperbolicQuadratic p.h).polarBilin _ c
  rw [unit_left_channels_pairing,unit_left_channels_pairing]
  have hh:=hf e _ (Submodule.mem_sup_left (one_primal_pin_stored a ha i e hv))
    _ (one_channel_in_tab b e (Pi.single j c))
  have he : oneNominalCoordinates p n (oneEndpointInjection i (v,0))=(jointInjection i v,0) := by
    apply Prod.ext
    · exact one_nominal_endpoint_primal i (v,0)
    · funext k
      cases i <;> cases k <;> rfl
  rw [←one_table_nominal_value,←one_table_nominal_value,he] at hh
  simpa only [oneChannelInjection,LinearMap.comp_apply,LinearEquiv.coe_coe,
    LinearMap.inr_apply,LinearEquiv.apply_symm_apply] using hh

theorem one_contract_pin_congr (P : Bool→Comp p.g→Space (Ray p n)) (T Q : OneCross p n)
    (h : ∀ e i j,∀ v∈P i e,
      unitLeftChannels p.h (oneTableOfCross T e) j (jointInjection i v)=
        unitLeftChannels p.h (oneTableOfCross Q e) j (jointInjection i v))
    (i j : Bool) (z : Profile p n) (hz : z∈oneEffectivePins P i) :
    oneContract T i j z=oneContract Q i j z := by
  simp only [oneContract,LinearMap.comp_apply,joint_matrix_functional_apply,joint_endpoint_component]
  apply sum_congr rfl
  intro e _
  have hZ:=((one_effective_mem P i z).mp hz).2 e
  generalize hze : z e=Z at hZ ⊢
  clear hze
  induction hZ using Submodule.span_induction with
  | mem Z hZ =>
    obtain ⟨v,hv,rfl⟩:=hZ
    rw [joint_matrix_injection_outer,mpair_outer,mpair_outer]
    have hT:=channel_quadratic_matrix_value p.h (unitLeftChannels p.h (oneTableOfCross T e) j)
      (jointInjection i v)
    have hQ:=channel_quadratic_matrix_value p.h (unitLeftChannels p.h (oneTableOfCross Q e) j)
      (jointInjection i v)
    change (channelQuadraticMatrix p.h _).toBilin' _ _=_ at hT hQ
    rw [Matrix.toBilin'_apply'] at hT hQ
    exact hT.trans ((congrArg (hyperbolicQuadratic p.h) (h e i j v hv)).trans hQ.symm)
  | zero => simp only [map_zero]
  | add a b _ _ ha hb => simp only [map_add,ha,hb]
  | smul c a _ ha => simp only [map_smul,ha]

theorem one_fits_contract (a b : ImagePlan (Comp p.g) (OneColumn p n))
    (ha : (onePinClosure p n).close a=a) (T Q : OneCross p n) (hf : oneFitsTable a b T Q)
    (i j : Bool) (z : Profile p n) (hz : z∈oneEffectivePins (oneEndpointPrimalPins a) i) :
    oneContract T i j z=oneContract Q i j z :=
  one_contract_pin_congr _ T Q (fun e i j v hv=>one_fits_channel_values a b ha T Q hf e i j hv) i j z hz

theorem one_flag_contract (a b : ImagePin (Comp p.g) (OneColumn p n) (2*N))
    (ha : (onePinClosure p n).close a.sp=a.sp) (T : OneCross p n)
    (x y : OneUnit p n N) (hx : imagePinAgree oneCoordinateImages a x)
    (hy : oneTableFlag b a (fun e=>(T e)ᵀ) y)
    (i j : Bool) (z : Profile p n) (hz : z∈oneEffectivePins (oneEndpointPrimalPins a.sp) i) :
    oneContract T i j z=oneFunctional (y j) (oneMomentEmbed (x i) z) := by
  apply (one_contract_pin_congr (oneEndpointPrimalPins a.sp) T (oneCrossMatrix x y) ?_ i j z hz).trans
    (one_contract_actual x y i j z ((one_effective_mem _ _ _).mp hz).1)
  intro e i j v hv
  rw [one_actual_table]
  exact one_flag_channel_values a b ha T x y hx hy e i j hv

def oneTableSafe (a b : ImagePlan (Comp p.g) (OneColumn p n)) (T : OneCross p n) :=
  ∀ e i j,∀ v∈oneEndpointPrimalPins a i e,
    unitLeftChannels p.h (oneTableOfCross T e) j (jointInjection i v)∈oneChannelPins b j e→v=0

theorem one_fits_safe (a b : ImagePlan (Comp p.g) (OneColumn p n))
    (ha : (onePinClosure p n).close a=a) (T Q : OneCross p n)
    (hf : oneFitsTable a b T Q) (hs : oneTableSafe a b Q) : oneTableSafe a b T := by
  intro e i j v hv hc
  rw [one_fits_channel_values a b ha T Q hf e i j hv] at hc
  exact hs e i j v hv hc

theorem one_safe_actual (a b : ImagePlan (Comp p.g) (OneColumn p n))
    (x y : OneUnit p n N) (h : onePinSafe (oneEndpointPrimalPins a) (oneChannelPins b) x y) :
    oneTableSafe a b (oneCrossMatrix x y) := by
  simpa only [oneTableSafe,onePinSafe,one_actual_table] using h

theorem one_safe_of_flags (a b : ImagePin (Comp p.g) (OneColumn p n) (2*N))
    (ha : (onePinClosure p n).close a.sp=a.sp) (T : OneCross p n)
    (x y : OneUnit p n N) (hx : imagePinAgree oneCoordinateImages a x)
    (hy : oneTableFlag b a (fun e=>(T e)ᵀ) y) (hs : oneTableSafe a.sp b.sp T) :
    onePinSafe (oneEndpointPrimalPins a.sp) (oneChannelPins b.sp) x y := by
  intro e i j v hv hc
  apply hs e i j v hv
  rw [one_flag_channel_values a b ha T x y hx hy e i j hv]
  exact hc

end
end Lax793645Proofs.Simplifications
