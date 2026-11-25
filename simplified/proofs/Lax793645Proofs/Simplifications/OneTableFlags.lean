import Lax793645Proofs.Simplifications.OneTableEnumeration
import Lax793645Proofs.Simplifications.OnePinInjection
import Lax793645Proofs.Simplifications.OneKeyPinSpaces

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Submodule Module Function
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N : ℕ}

theorem one_primal_pin_stored (a : ImagePlan (Comp p.g) (OneColumn p n))
    (ha : (onePinClosure p n).close a=a) (i : Bool) (e : Comp p.g)
    {v : Ray p n} (hv : v∈oneEndpointPrimalPins a i e) :
    oneEndpointInjection i (v,0)∈a e := by
  obtain ⟨u,⟨w,hw,rfl⟩,rfl⟩:=hv
  rw [←congrFun ha e]
  apply Submodule.mem_map.mpr
  refine ⟨oneBlockCoordinates p n (oneEndpointInjection i
    (jointProjection i (oneNominalCoordinates p n w).1,0)),?_,
    (oneBlockCoordinates p n).symm_apply_apply _⟩
  apply Submodule.mem_pi.mpr
  intro b _
  rcases b with j|j
  · by_cases h:i=j
    · subst j
      refine ⟨oneBlockCoordinates p n w,⟨w,hw,rfl⟩,?_⟩
      simp [oneBlockCoordinates,oneEndpointInjection,oneEndpointCoordinates,
        jointProjection,oneNominalCoordinates]
    · convert (Submodule.zero_mem _) using 1
      ext r
      simp [oneBlockCoordinates,oneEndpointInjection,oneEndpointCoordinates,
        LinearMap.single_apply,h]
  · rcases j with j|j <;> by_cases hij:i=j <;>
      convert (Submodule.zero_mem _) using 1 <;>
      ext r <;>
      simp [oneBlockCoordinates,oneEndpointInjection,oneEndpointCoordinates,
        LinearMap.single_apply,hij]

theorem one_channel_in_tab (a : ImagePlan (Comp p.g) (OneColumn p n))
    (e : Comp p.g) (c : Bool→Hyperbolic p.h) : oneChannelInjection p n c∈oneTabSpace a e :=
  Submodule.mem_sup_right ⟨c,rfl⟩

theorem one_cross_value (x y : OneUnit p n N) (e : Comp p.g) (v w : Vec (OneColumn p n)) :
    evmat (oneCrossMatrix x y e) v w=
      oneAmbientPolar N (oneCoordinateImages x e*ᵥv) (oneCoordinateImages y e*ᵥw) := by
  rw [←one_table_nominal_value,one_actual_table,one_coordinate_images_apply,
    one_coordinate_images_apply]
  simp only [oneAmbientPolar,LinearMap.compl₁₂_apply,LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply]
  rfl

def oneTableFlag (a b : ImagePin (Comp p.g) (OneColumn p n) (2*N))
    (T : OneCross p n) (x : OneUnit p n N) :=
  ∀ e,∀ v∈oneTabSpace a.sp e,∀ w∈b.sp e,
    evmat (T e) v w=oneAmbientPolar N (oneCoordinateImages x e*ᵥv) (b.target e*ᵥw)

theorem one_table_flag_actual (a b : ImagePin (Comp p.g) (OneColumn p n) (2*N))
    (x y : OneUnit p n N) (hy : imagePinAgree oneCoordinateImages b y) :
    oneTableFlag a b (oneCrossMatrix x y) x := by
  intro e v _ w hw
  rw [one_cross_value,hy e w hw]

theorem one_table_flag_fits (a b : ImagePin (Comp p.g) (OneColumn p n) (2*N))
    (T Q : OneCross p n) (hfit : oneFitsTable a.sp b.sp T Q)
    (x : OneUnit p n N) (hx : oneTableFlag a b Q x) : oneTableFlag a b T x :=
  fun e v hv w hw=>(hfit e v hv w (Submodule.mem_sup_left hw)).trans (hx e v hv w hw)

theorem one_table_flag_rows (a b : ImagePin (Comp p.g) (OneColumn p n) (2*N))
    (T : OneCross p n) (x y : OneUnit p n N)
    (hx : imagePinAgree oneCoordinateImages a x)
    (hy : oneTableFlag b a (fun e=>(T e)ᵀ) y) :
    ∀ e,∀ v∈a.sp e,∀ w∈oneTabSpace b.sp e,
      evmat (T e) v w=evmat (oneCrossMatrix x y e) v w := by
  intro e v hv w hw
  have hh:=hy e w hw v hv
  rw [evmat_transpose,←hx e v hv] at hh
  rw [hh,one_cross_value]
  change (hyperbolicMatrix N).toQuadraticForm'.polarBilin _ _=
    (hyperbolicMatrix N).toQuadraticForm'.polarBilin _ _
  exact binary_polar_symm _ _ _

/-- Opposite table flags determine the full channel image of each
stored primal pin; they do not assume independent selected-key images. -/
theorem one_flag_channel_values (a b : ImagePin (Comp p.g) (OneColumn p n) (2*N))
    (ha : (onePinClosure p n).close a.sp=a.sp) (T : OneCross p n)
    (x y : OneUnit p n N) (hx : imagePinAgree oneCoordinateImages a x)
    (hy : oneTableFlag b a (fun e=>(T e)ᵀ) y)
    (e : Comp p.g) (i j : Bool) {v : Ray p n} (hv : v∈oneEndpointPrimalPins a.sp i e) :
    unitLeftChannels p.h (oneTableOfCross T e) j (jointInjection i v)=
      unitLeftChannels p.h (oneUnitActual x y e) j (jointInjection i v) := by
  apply (LinearMap.BilinForm.toDual (hyperbolicQuadratic p.h).polarBilin
    (hyperbolic_nondegenerate p.h)).injective
  apply LinearMap.ext
  intro c
  change (hyperbolicQuadratic p.h).polarBilin _ c=(hyperbolicQuadratic p.h).polarBilin _ c
  rw [unit_left_channels_pairing,unit_left_channels_pairing,←one_actual_table x y e]
  have hh:=one_table_flag_rows a b T x y hx hy e _ (one_primal_pin_stored a.sp ha i e hv)
    _ (one_channel_in_tab b.sp e (Pi.single j c))
  have he : oneNominalCoordinates p n (oneEndpointInjection i (v,0))=(jointInjection i v,0) := by
    apply Prod.ext
    · exact one_nominal_endpoint_primal i (v,0)
    · funext k
      cases i <;> cases k <;> rfl
  rw [←one_table_nominal_value,←one_table_nominal_value,he] at hh
  simpa only [oneChannelInjection,LinearMap.comp_apply,LinearEquiv.coe_coe,
    LinearMap.inr_apply,LinearEquiv.apply_symm_apply] using hh

end
end Lax793645Proofs.Simplifications
