import Lax793645Proofs.Simplifications.JointSelectedReplacement
import Lax793645Proofs.Simplifications.OneUnaryRecords

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Module Submodule
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {p : Shape} {n : ℕ}

def oneCrossOfTables (T : Comp p.g→LinearMap.BilinForm F (OneUnitFull p n)) : OneCross p n:=
  fun e=>LinearMap.toMatrix₂' F ((T e).compl₁₂
    (oneNominalCoordinates p n).toLinearMap (oneNominalCoordinates p n).toLinearMap)

theorem one_cross_table_inverse (T : Comp p.g→LinearMap.BilinForm F (OneUnitFull p n))
    (e : Comp p.g) : oneTableOfCross (oneCrossOfTables T) e=T e := by
  have he : (oneCrossOfTables T e).toBilin'=(T e).compl₁₂
      (oneNominalCoordinates p n).toLinearMap (oneNominalCoordinates p n).toLinearMap:=
    Matrix.toBilin'_toMatrix' _
  apply LinearMap.ext
  intro v
  apply LinearMap.ext
  intro w
  simp only [oneTableOfCross,he,LinearMap.compl₁₂_apply,LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]

theorem unit_table_left_channels (h : ℕ) {A B : Type} [AddCommGroup A] [Module F A]
    [AddCommGroup B] [Module F B] (M : A→ₗ[F]B→ₗ[F]F)
    (D : LinearMap.BilinForm F (UnitChannels h))
    (gA : Bool→A→ₗ[F]Hyperbolic h) (gB : Bool→B→ₗ[F]Hyperbolic h) (j : Bool) :
    unitLeftChannels h (unitQuadraticTable h M D gA gB) j=gA j := by
  apply LinearMap.ext
  intro a
  apply (LinearMap.BilinForm.toDual (hyperbolicQuadratic h).polarBilin (hyperbolic_nondegenerate h)).injective
  apply LinearMap.ext
  intro c
  exact (unit_left_channels_pairing h _ j a c).trans (unit_quadratic_table_left h M D gA gB j a c)

theorem unit_table_right_channels (h : ℕ) {A B : Type} [AddCommGroup A] [Module F A]
    [AddCommGroup B] [Module F B] (M : A→ₗ[F]B→ₗ[F]F)
    (D : LinearMap.BilinForm F (UnitChannels h))
    (gA : Bool→A→ₗ[F]Hyperbolic h) (gB : Bool→B→ₗ[F]Hyperbolic h) (i : Bool) :
    unitRightChannels h (unitQuadraticTable h M D gA gB) i=gB i := by
  apply LinearMap.ext
  intro b
  apply (LinearMap.BilinForm.toDual (hyperbolicQuadratic h).polarBilin (hyperbolic_nondegenerate h)).injective
  apply LinearMap.ext
  intro c
  change (hyperbolicQuadratic h).polarBilin _ c=(hyperbolicQuadratic h).polarBilin _ c
  rw [binary_polar_symm,unit_right_channels_pairing,unit_quadratic_table_right,binary_polar_symm]

/-- Simultaneous reciprocal realization, with the baseline derived from
the actual cross table. Mixed-endpoint frozen kernels are retained. -/
theorem one_reciprocal_realization
    (T : Comp p.g→LinearMap.BilinForm F (OneUnitFull p n))
    (PA PB : Comp p.g→Space (JointRay p n))
    (CA CB : Bool→Comp p.g→Space (Hyperbolic p.h))
    (MA MB : Bool→JointProfile p n) (f c r : ℕ)
    (hPA : ∀ e,dim (PA e)≤f) (hPB : ∀ e,dim (PB e)≤f)
    (hCA : ∀ i e,dim (CA i e)≤c) (hCB : ∀ j e,dim (CB j e)≤c)
    (hMA : ∀ j e,(MA j e).rank≤r) (hMB : ∀ i e,(MB i e).rank≤r)
    (hobsA : ∀ j x,x∈jointXspace→
      x∈jointQuadraticConstraints PA (fun e=>frozenChannelKernel p.h (PA e) (CB j e)
        ((unitLeftChannels p.h (T e) j).domRestrict (PA e)))→
      jointMatrixFunctional (MA j) x=
        jointMatrixFunctional (fun e=>channelQuadraticMatrix p.h (unitLeftChannels p.h (T e) j)) x)
    (hobsB : ∀ i x,x∈jointXspace→
      x∈jointQuadraticConstraints PB (fun e=>frozenChannelKernel p.h (PB e) (CA i e)
        ((unitRightChannels p.h (T e) i).domRestrict (PB e)))→
      jointMatrixFunctional (MB i) x=
        jointMatrixFunctional (fun e=>channelQuadraticMatrix p.h (unitRightChannels p.h (T e) i)) x)
    (hroom : r+(f+c)+jointCompressionRank p f (2*f+(f+c))+5*c+6*f+2≤p.h) :
    ∃ (Q : OneCross p n) (QA QB : Bool→JointProfile p n),
      (∀ j e v,hyperbolicQuadratic p.h (unitLeftChannels p.h (oneTableOfCross Q e) j v)=
        (QA j e).toQuadraticForm' v) ∧
      (∀ i e v,hyperbolicQuadratic p.h (unitRightChannels p.h (oneTableOfCross Q e) i v)=
        (QB i e).toQuadraticForm' v) ∧
      (∀ j x,x∈jointXspace→jointMatrixFunctional (QA j) x=jointMatrixFunctional (MA j) x) ∧
      (∀ i x,x∈jointXspace→jointMatrixFunctional (QB i) x=jointMatrixFunctional (MB i) x) ∧
      (∀ e a d,a∈PA e→(∀ i,d i∈CA i e)→∀ v,oneTableOfCross Q e (a,d) v=T e (a,d) v) ∧
      (∀ e b d,b∈PB e→(∀ j,d j∈CB j e)→∀ v,oneTableOfCross Q e v (b,d)=T e v (b,d)) := by
  classical
  choose QA gA hqA hfA hpA hoA hrA using fun j=>joint_channel_replacement p.h PA (CB j)
    (fun e=>unitLeftChannels p.h (T e) j) (MA j)
    (fun e=>channelQuadraticMatrix p.h (unitLeftChannels p.h (T e) j))
    (fun e v=>channel_quadratic_matrix_value p.h _ v)
    f c r hPA (hCB j) (hMA j) (hobsA j) hroom
  choose QB gB hqB hfB hpB hoB hrB using fun i=>joint_channel_replacement p.h PB (CA i)
    (fun e=>unitRightChannels p.h (T e) i) (MB i)
    (fun e=>channelQuadraticMatrix p.h (unitRightChannels p.h (T e) i))
    (fun e v=>channel_quadratic_matrix_value p.h _ v)
    f c r hPB (hCA i) (hMB i) (hobsB i) hroom
  let R (e : Comp p.g):=unitQuadraticTable p.h (unitPrimalTable p.h (T e))
    (unitChannelTable p.h (T e)) (fun j=>gA j e) (fun i=>gB i e)
  let Q:=oneCrossOfTables R
  have he (e : Comp p.g) : oneTableOfCross Q e=R e:=one_cross_table_inverse R e
  refine ⟨Q,QA,QB,?_,?_,hoA,hoB,?_,?_⟩
  · intro j e v
    rw [he,unit_table_left_channels]
    exact hqA j e v
  · intro i e v
    rw [he,unit_table_right_channels]
    exact hqB i e v
  · intro e a d ha hd v
    rw [he]
    have hh:=(unit_quadratic_frozen_rows p.h (unitPrimalTable p.h (T e))
      (unitChannelTable p.h (T e)) (fun j=>gA j e) (unitLeftChannels p.h (T e))
      (fun i=>gB i e) (unitRightChannels p.h (T e)) (PA e) (PB e)
      (fun i=>CA i e) (fun j=>CB j e) (fun j=>hfA j e) (fun i=>hfB i e)
      (fun j=>hpA j e) (fun i=>hpB i e)).1 a d ha hd v
    simpa only [unit_table_coordinates] using hh
  · intro e b d hb hd v
    rw [he]
    have hh:=(unit_quadratic_frozen_rows p.h (unitPrimalTable p.h (T e))
      (unitChannelTable p.h (T e)) (fun j=>gA j e) (unitLeftChannels p.h (T e))
      (fun i=>gB i e) (unitRightChannels p.h (T e)) (PA e) (PB e)
      (fun i=>CA i e) (fun j=>CB j e) (fun j=>hfA j e) (fun i=>hfB i e)
      (fun j=>hpA j e) (fun i=>hpB i e)).2 b d hb hd v
    simpa only [unit_table_coordinates] using hh

end
end Lax793645Proofs.Simplifications
