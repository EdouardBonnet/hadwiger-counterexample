import Lax793645Proofs.Simplifications.FreeChannelCoordinates

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open LinearMap Module
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {B C V : Type} [AddCommGroup B] [Module F B] [AddCommGroup C] [Module F C]
  [AddCommGroup V] [Module F V] [FiniteDimensional F B] [FiniteDimensional F C]
  [FiniteDimensional F V] [Fintype B] [Fintype C] [Fintype V]
  [Fintype (B×C→ₗ[F]V)] [Fintype (C→ₗ[F]V)] [Fintype (QuadraticFull B C→ₗ[F]V)]

/-- The unrestricted Y channel has density at most two. Unlike the
whole-pair bound, this constant does not grow with the channel dimension. -/
theorem quadratic_free_channel_cap (q : QuadraticForm F V) (Q : QuadraticForm F B)
    (hroom : dim B+2*dim C+1≤dim V) (Y : C→ₗ[F]V) :
    mapW (quadraticChannelRaw (C:=C) q Q) (fun f=>f.comp quadraticYIn) Y≤2*unif Y := by
  let E : (QuadraticFull B C→ₗ[F]V)≃((B×C→ₗ[F]V)×(C→ₗ[F]V)):=quadraticChannelSplit.toEquiv
  have hl : mapW (quadraticChannelRaw (C:=C) q Q) E=
      unifOn (fun xy=>(quadraticPXValid q Q xy.1) ∧Function.Injective (xy.1.coprod xy.2)) := by
    rw [quadraticChannelRaw,uniform_condition_equiv]
    congr 1
    funext xy
    exact propext ((quadratic_channel_split_valid q Q (E.symm xy)).trans (by
      have hh : quadraticChannelSplit (E.symm xy)=xy:=E.apply_symm_apply xy
      rw [hh]))
  have hc:=free_channel_marginal (B:=B×C) (C:=C) (V:=V) (quadraticPXValid q Q) (fun X hX=>hX.1)
    (by simpa only [dim,Module.finrank_prod,two_mul,add_assoc] using hroom) Y
  rw [←hl,mapW_nested] at hc
  have he : Prod.snd∘E=(fun f : QuadraticFull B C→ₗ[F]V=>f.comp quadraticYIn) := by
    funext f
    apply LinearMap.ext
    exact fun c=>quadratic_channel_split_second f c
  rw [he] at hc
  exact hc

end
end Lax793645Proofs.Simplifications
