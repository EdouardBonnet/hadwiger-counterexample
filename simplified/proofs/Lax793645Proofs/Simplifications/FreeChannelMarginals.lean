import Lax793645Proofs.Simplifications.FreeLinearExtensions
import Lax793645Proofs.Simplifications.FreeCoordinateConditioning
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.ChannelFrameLaws

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open LinearMap Module
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {B C V : Type} [AddCommGroup B] [Module F B] [AddCommGroup C] [Module F C]
  [AddCommGroup V] [Module F V] [FiniteDimensional F B] [FiniteDimensional F C]
  [FiniteDimensional F V] [Fintype B] [Fintype C] [Fintype V]
  [Fintype (B→ₗ[F]V)] [Fintype (C→ₗ[F]V)]

/-- Any restrictions on the old columns are allowed. Fresh unconstrained
columns have density at most two once the ambient space has one spare bit
beyond the entire nominal dimension. -/
theorem free_channel_marginal (P : (B→ₗ[F]V)→Prop)
    (hP : ∀ X,P X→Function.Injective X) (hroom : dim B+dim C+1≤dim V)
    (Y : C→ₗ[F]V) :
    mapW (unifOn (fun xy : (B→ₗ[F]V)×(C→ₗ[F]V)=>P xy.1 ∧
      Function.Injective (xy.1.coprod xy.2))) Prod.snd Y≤2*unif Y := by
  have hh (X : B→ₗ[F]V) (hx : P X) : (1/2:ℝ)≤
      pr unif (fun Y : C→ₗ[F]V=>Function.Injective (X.coprod Y)) := by
    have hb:=free_extension_failure (C:=C) X (hP X hx)
    have hr : ((dim B:ℝ)+dim C-dim V)≤-1 := by
      have hh : (dim B:ℝ)+dim C+1≤dim V:=by exact_mod_cast hroom
      linarith
    have hbp:=bp_le hr
    norm_num [bp_neg,bp_one] at hbp
    have he:=pr_not (unif : Wgt (C→ₗ[F]V))
      (fun Y=>Function.Injective (X.coprod Y))
    rw [unif_law.total] at he
    linarith
  have he:=free_coordinate_conditioning (unif : Wgt (B→ₗ[F]V))
    (unif : Wgt (C→ₗ[F]V)) unif_law.nz unif_law.nz P
    (fun X Y=>Function.Injective (X.coprod Y)) (by norm_num : (0:ℝ)<1/2) hh Y
  rw [←pair_unif,on_unif] at he
  simpa using he

end
end Lax793645Proofs.Simplifications
