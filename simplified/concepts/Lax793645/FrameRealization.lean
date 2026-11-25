import Lax793645.ConstructionData

/-!
---
title: Realizing four witness lists
type: theorem
---
A safe frozen table with matching keys can be completed when the scalar recipes and
binary prescriptions hold. The two reciprocal prescriptions can be realized together,
preserving the specified rows and columns.
-/

namespace Lax793645.FrameRealization

section
open Lax793645.ConstructionData.Binary
open Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Matrix LinearMap Module Submodule
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n : ℕ}

axiom one_reciprocal_realization
    (T : Comp p.g→ LinearMap.BilinForm F (OneUnitFull p n))
    (PA PB : Comp p.g→ Space (JointRay p n))
    (CA CB : Bool→ Comp p.g→ Space (Hyperbolic p.h))
    (MA MB : Bool→ JointProfile p n) (f c r : ℕ)
    (hPA : ∀ e,dim (PA e)≤ f) (hPB : ∀ e,dim (PB e)≤ f)
    (hCA : ∀ i e,dim (CA i e)≤ c) (hCB : ∀ j e,dim (CB j e)≤ c)
    (hMA : ∀ j e,(MA j e).rank≤ r) (hMB : ∀ i e,(MB i e).rank≤ r)
    (hobsA : ∀ j x,x∈jointXspace→
      x∈jointQuadraticConstraints PA (fun e=> frozenChannelKernel p.h (PA e) (CB j e)
        ((unitLeftChannels p.h (T e) j).domRestrict (PA e)))→
      jointMatrixFunctional (MA j) x=
        jointMatrixFunctional (fun e=> channelQuadraticMatrix p.h (unitLeftChannels p.h (T e) j)) x)
    (hobsB : ∀ i x,x∈jointXspace→
      x∈jointQuadraticConstraints PB (fun e=> frozenChannelKernel p.h (PB e) (CA i e)
        ((unitRightChannels p.h (T e) i).domRestrict (PB e)))→
      jointMatrixFunctional (MB i) x=
        jointMatrixFunctional (fun e=> channelQuadraticMatrix p.h (unitRightChannels p.h (T e) i)) x)
    (hroom : r+(f+c)+jointCompressionRank p f (2* f+(f+c))+5* c+6* f+2≤ p.h) :
    ∃ (Q : OneCross p n) (QA QB : Bool→ JointProfile p n),
      (∀ j e v,hyperbolicQuadratic p.h (unitLeftChannels p.h (oneTableOfCross Q e) j v)=
        (QA j e).toQuadraticForm' v) ∧
      (∀ i e v,hyperbolicQuadratic p.h (unitRightChannels p.h (oneTableOfCross Q e) i v)=
        (QB i e).toQuadraticForm' v) ∧
      (∀ j x,x∈jointXspace→ jointMatrixFunctional (QA j) x=jointMatrixFunctional (MA j) x) ∧
      (∀ i x,x∈jointXspace→ jointMatrixFunctional (QB i) x=jointMatrixFunctional (MB i) x) ∧
      (∀ e a d,a∈PA e→(∀ i,d i∈CA i e)→∀ v,oneTableOfCross Q e (a,d) v=T e (a,d) v) ∧
      (∀ e b d,b∈PB e→(∀ j,d j∈CB j e)→∀ v,oneTableOfCross Q e v (b,d)=T e v (b,d))

end

end Lax793645.FrameRealization
