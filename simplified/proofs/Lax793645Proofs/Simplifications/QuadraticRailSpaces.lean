import Lax793645Proofs.Simplifications.QuadraticGramFourCorners

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function LinearMap Module Submodule
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I : Type} [Fintype I] [DecidableEq I]

def symmetricRail (E : Rail I) : Space (Mat I I) where
  carrier:={M | Mᵀ=M ∧ withinRail M E}
  zero_mem':=⟨by simp,fun _ _ _=>rfl⟩
  add_mem' hx hy:=⟨by rw [transpose_add,hx.1,hy.1],fun i j h=>by
    rw [Matrix.add_apply,hx.2 i j h,hy.2 i j h,add_zero]⟩
  smul_mem' c M hM:=⟨by rw [transpose_smul,hM.1],fun i j h=>by
    change c*M i j=0; rw [hM.2 i j h,mul_zero]⟩

instance symmetricRailFintype (E : Rail I) : Fintype (symmetricRail E):=Fintype.ofFinite _
instance symmetricRailDualFintype (E : Rail I) : Fintype (symmetricRail E →ₗ[F] F):=
  Fintype.ofInjective (fun f=>⇑f) DFunLike.coe_injective

def quadraticRailRead (E : Rail I) : Mat I I →ₗ[F] (symmetricRail E →ₗ[F] F):=
  (symmetricRail E).subtype.dualMap.comp matrixPairing

theorem quadratic_rail_read_value (E : Rail I) (G : Mat I I) (M : symmetricRail E) :
    quadraticRailRead E G M=mpair M.val G:=mpair_comm G M.val

theorem quadratic_rail_read_surjective (E : Rail I) : Surjective (quadraticRailRead E) := by
  exact ((LinearMap.dualMap_surjective_of_injective (symmetricRail E).subtype_injective)).comp
    (matrixPairing.toDual matrix_pairing_nondegenerate).surjective

theorem quadratic_rail_read_uniform (E : Rail I) :
    mapW (unif : Wgt (Mat I I)) (quadraticRailRead E)=unif :=
  map_unif_surjective (quadraticRailRead E) (quadratic_rail_read_surjective E)

theorem quadratic_traced_read {N : ℕ} (E : Rail I) (Z : Mat I I) (x : KeyCoordinates I N) :
    quadraticTraced E Z x ↔ quadraticRailRead E ((keyPlus x)ᵀ*keyMinus x)=quadraticRailRead E Z := by
  constructor
  · intro h
    apply LinearMap.ext
    intro M
    rw [quadratic_rail_read_value,quadratic_rail_read_value]
    simpa only [gramPrimitive,layer_form] using h M.val M.property.1 M.property.2
  · intro h M hs hm
    have hh:=LinearMap.congr_fun h ⟨M,hs,hm⟩
    simpa only [quadratic_rail_read_value,gramPrimitive,layer_form] using hh

/-- Fourier expansion over the exact symmetric coefficient space. Every
coefficient has normalized absolute mass, with no redundant equations. -/
theorem quadratic_rail_expansion {N : ℕ} (E : Rail I) (Z : Mat I I) (x : KeyCoordinates I N) :
    ind (quadraticTraced E Z x)=avg unif (fun M : symmetricRail E=>
      wsign (mpair M.val Z)*wsign (gramPrimitive M.val x)) := by
  let L:=quadraticRailRead E (((keyPlus x)ᵀ*keyMinus x)+Z)
  have he : (fun M : symmetricRail E=>wsign (mpair M.val Z)*wsign (gramPrimitive M.val x))=
      (fun M=>wsign (L M)) := by
    funext M
    rw [←wsign_add]
    congr 1
    rw [show L M=mpair M.val (((keyPlus x)ᵀ*keyMinus x)+Z) from quadratic_rail_read_value E _ M,
      map_add,gramPrimitive,layer_form]
    exact add_comm _ _
  rw [he,wsign_lin,quadratic_traced_read]
  congr 1
  apply propext
  change _ ↔ quadraticRailRead E (((keyPlus x)ᵀ*keyMinus x)+Z)=0
  rw [map_add,←ZModModule.sub_eq_add,sub_eq_zero]

end
end Lax793645Proofs.Simplifications
