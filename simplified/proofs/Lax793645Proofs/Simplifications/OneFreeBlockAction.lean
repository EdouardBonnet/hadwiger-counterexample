import Lax793645Proofs.Simplifications.OneUnaryReference
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.FrameRotations

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Function Finset
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N : ℕ}

def oneBreeze (p : Shape) (c : Flit n) : Ray p n≃ₗ[F]Ray p n where
  toLinearMap:=(blitz p c.L).mulVecLin
  invFun:=(blitz p c.R).mulVec
  left_inv x:=by
    change blitz p c.R*ᵥ(blitz p c.L*ᵥx)=x
    rw [mulVec_mulVec,←blitz_mul,c.RL,blitz_one,one_mulVec]
  right_inv x:=by
    change blitz p c.L*ᵥ(blitz p c.R*ᵥx)=x
    rw [mulVec_mulVec,←blitz_mul,c.LR,blitz_one,one_mulVec]

def oneBoom (p : Shape) (c : Flit n) : OneFull p n≃ₗ[F]OneFull p n:=
  (oneBreeze p c).prodCongr (LinearEquiv.refl F _)

def oneFuse (p : Shape) (c : Flit n) (N : ℕ) : OneFrame p n N≃OneFrame p n N where
  toFun P:=P.comp (oneBoom p c).toLinearMap
  invFun P:=P.comp (oneBoom p c).symm.toLinearMap
  left_inv P:=by
    apply LinearMap.ext
    intro x
    exact congrArg P ((oneBoom p c).apply_symm_apply x)
  right_inv P:=by
    apply LinearMap.ext
    intro x
    exact congrArg P ((oneBoom p c).symm_apply_apply x)

def oneKite (p : Shape) (c : Flit n) (N : ℕ) : OneOrient p n N≃OneOrient p n N:=
  Equiv.piCongrRight (fun _=>oneFuse p c N)

theorem one_breeze_self (c : Flit n) (m : Mixer p n) (v : Ray p n) :
    (selfM p n m.mixM).toQuadraticForm' (oneBreeze p c v)=
      (selfM p n m.mixM).toQuadraticForm' v := by
  rw [←matrix_quadratic_outer,←matrix_quadratic_outer]
  change mpair (selfM p n m.mixM) (vecMulVec ((blitz p c.L)*ᵥv) ((blitz p c.L)*ᵥv))=_
  rw [←liftM_outer,mpair_liftM]
  change mpair (pullM (blitz p c.L) (blitz p c.L) (selfM p n m.mixM)) _=_
  rw [blitz_fixes]

theorem one_fuse_valid (c : Flit n) (m : Mixer p n) (P : OneFrame p n N)
    (hP : quadraticChannelValid (hyperbolicMatrix N).toQuadraticForm'
      (selfM p n m.mixM).toQuadraticForm' P) :
    quadraticChannelValid (hyperbolicMatrix N).toQuadraticForm'
      (selfM p n m.mixM).toQuadraticForm' (oneFuse p c N P) := by
  obtain ⟨hinj,hval,hrow⟩:=quadratic_channel_frame_data _ _ P hP
  refine ⟨hinj.comp (oneBoom p c).injective,?_,?_⟩
  · apply QuadraticMap.ext
    intro v
    change (hyperbolicMatrix N).toQuadraticForm' (P (quadraticPrimalIn (oneBreeze p c v)))=_
    rw [hval,one_breeze_self]
  · intro a v
    change ((hyperbolicMatrix N).toQuadraticForm'.comp (oneFuse p c N P)).polarBilin
      (quadraticXIn a) (quadraticPrimalIn v)=0
    rw [QuadraticMap.polarBilin_comp]
    change (hyperbolicMatrix N).toQuadraticForm'.polarBilin
      (P (oneBoom p c (quadraticXIn a))) (P (quadraticPrimalIn (oneBreeze p c v)))=0
    have hx : oneBoom p c (quadraticXIn a)=quadraticXIn a := by
      change (oneBreeze p c 0,(a,0))=(0,(a,0))
      rw [map_zero]
    rw [hx]
    exact hrow a (oneBreeze p c v)

theorem one_kite_weights (c : Flit n) (m : Mixer p n) (o : OneOrient p n N) :
    oneRaw m N (oneKite p c N o)=oneRaw m N o := by
  unfold oneRaw prodW
  apply Finset.prod_congr rfl
  intro e _
  have hv : quadraticChannelValid (hyperbolicMatrix N).toQuadraticForm'
      (selfM p n m.mixM).toQuadraticForm' (oneKite p c N o e) ↔
      quadraticChannelValid (hyperbolicMatrix N).toQuadraticForm'
        (selfM p n m.mixM).toQuadraticForm' (o e) := by
    constructor
    · intro h
      have hh:=one_fuse_valid c.sym m _ h
      have he : oneFuse p c.sym N (oneKite p c N o e)=o e := by
        apply LinearMap.ext
        intro v
        change o e ((oneBoom p c) (oneBoom p c.sym v))=o e v
        have hr : oneBoom p c.sym=(oneBoom p c).symm := rfl
        rw [hr,(oneBoom p c).apply_symm_apply]
      rwa [he] at hh
    · exact one_fuse_valid c m (o e)
  simp only [quadraticChannelRaw,unifOn_val,hv]

theorem one_kite_keys (c : Flit n) (v : Template.Solo p)
    (o : OneOrient p n N) (z : Knobs p.g n) :
    oneDesc v z (oneKite p c N o)=oneDesc v (Move.vault p c z) o := by
  funext e a
  change onePrimal (o e.val) ((blitz p c.L)*ᵥspring p (v.t ()) (v.s ()) (v.f ()) z) a=_
  rw [sailsZ]
  rfl

end
end Lax793645Proofs.Simplifications
