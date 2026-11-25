import Lax793645Proofs.Simplifications.OneScalarRealization

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Module Submodule
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {p : Shape} {n : ℕ}

theorem one_endpoint_pin_sum (a : ImagePlan (Comp p.g) (OneColumn p n)) (i : Bool) :
    (∑ e,dim (oneEndpointPrimalPins a i e)) ≤ imagePlanRank a :=
  Finset.sum_le_sum (fun e _=>one_endpoint_primal_pin_dimension a i e)

theorem image_plan_component_dimension {C D : Type} [Fintype C] [Fintype D]
    (a : ImagePlan C D) (e : C) : dim (a e) ≤ imagePlanRank a :=
  Finset.single_le_sum (fun j _=>Nat.zero_le (dim (a j))) (Finset.mem_univ e)

/-- Effective profiles retain the same bounded total-rank interface as
the old two-mode construction. -/
theorem one_effective_rank (a : ImagePlan (Comp p.g) (OneColumn p n)) (i : Bool)
    (z : Profile p n) (hz : z∈oneEffectivePins (oneEndpointPrimalPins a) i) :
    totalRank z ≤ imagePlanRank a := by
  apply (Finset.sum_le_sum (fun e _=>?_)).trans (one_endpoint_pin_sum a i)
  exact Submodule.finrank_mono
    ((box_mem ..).mp (quadraticSquares_data (((one_effective_mem _ _ _).mp hz).2 e)).2).1

theorem pi_subspace_dimension {V J : Type} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] [Fintype J] (S : J→Submodule F V) :
    dim (Submodule.pi Set.univ S)≤∑ i,dim (S i) := by
  let T:=Submodule.pi Set.univ S
  let f : T→ₗ[F](∀ i,S i):={
    toFun x i:=⟨x.val i,x.property i (Set.mem_univ i)⟩
    map_add' _ _:=rfl
    map_smul' _ _:=rfl }
  have hf : Function.Injective f:=fun x y h=>Subtype.ext
    (funext (fun i=>congrArg Subtype.val (congrFun h i)))
  exact (LinearMap.finrank_le_finrank_of_injective hf).trans_eq (Module.finrank_pi_fintype F)

theorem one_effective_dimension (a : ImagePlan (Comp p.g) (OneColumn p n)) (i : Bool) :
    dim (oneEffectivePins (oneEndpointPrimalPins a) i)≤(imagePlanRank a)^2 := by
  let P:=oneEndpointPrimalPins a i
  have hh : oneEffectivePins (oneEndpointPrimalPins a) i≤
      Submodule.pi Set.univ (fun e=>box (P e) (P e)) := by
    intro z hz e _
    exact (quadraticSquares_data (((one_effective_mem _ _ _).mp hz).2 e)).2
  apply ((Submodule.finrank_mono hh).trans (pi_subspace_dimension _)).trans
  simp_rw [box_dim]
  calc
    ∑ e,dim (P e)*dim (P e)≤∑ e,dim (P e)*imagePlanRank a:=
      Finset.sum_le_sum (fun e _=>Nat.mul_le_mul_left _
        ((one_endpoint_primal_pin_dimension a i e).trans (image_plan_component_dimension a e)))
    _≤(imagePlanRank a)^2:=by
      rw [←Finset.sum_mul,pow_two]
      exact Nat.mul_le_mul_right _ (one_endpoint_pin_sum a i)

/-- Testing a basis is exactly equivalent to the entire effective-space
condition, so only the square of the pin budget many scalar bits occur. -/
theorem one_effective_test_basis (P : Bool→Comp p.g→Space (Ray p n)) (i : Bool)
    (f g : Profile p n→ₗ[F]F) :
    (∀ z∈oneEffectivePins P i,f z=g z)↔
    ∀ j : Fin (dim (oneEffectivePins P i)),
      f ((Module.finBasis F (oneEffectivePins P i) j).val)=
        g ((Module.finBasis F (oneEffectivePins P i) j).val) := by
  constructor
  · exact fun h j=>h _ (Module.finBasis F (oneEffectivePins P i) j).property
  intro h z hz
  have he : f.comp (oneEffectivePins P i).subtype=g.comp (oneEffectivePins P i).subtype:=
    (Module.finBasis F (oneEffectivePins P i)).ext h
  exact DFunLike.congr_fun he ⟨z,hz⟩

end
end Lax793645Proofs.Simplifications
