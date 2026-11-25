import Lax793645.ConstructionData

/-!
---
title: Four parity bits for two marked units
type: theorem
---
After retaining a fixed positive mass, the four readings either have small bias in
every nonconstant character, or the marked offsets admit a bounded cover and the
characters involving a single endpoint have exponentially small bias.
-/

namespace Lax793645.PhaseAlternative

section
open Lax793645.ConstructionData.Binary
open Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Matrix LinearMap Module Submodule Function Finset
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N r : ℕ}

axiom one_phase_alternative {w : Wgt (OneUnit p n N)}
    (marks : OneUnit p n N→ Bool→ Profile p n)
    {c l ψ ε L H : ℝ} {m b k d : ℕ}
    (mix : Mixer p n) (hr : OnePhaseReady p n N m b r k d mix c l ψ ε L H)
    (hw : IsLaw w)
    (hk : ∀ i o,mapW w (fun x=> x i) o≤ L* oneRaw mix N o)
    (hv : ∀ x,w x≤ H* oneUnitRaw mix N x)
    (hmarks : ∀ x,w x≠0→∀ i,marks x i∈Xspace p n)
    (hh : ∀ x,w x≠0→ oneMarkedDelta x (marks x)≠0 ∧totalRank (marks x true)≤ r)
    (hK : ∀ x,epoch p (oneMarkedDelta x (marks x))≤ r) :
    ∃ P : OneUnit p n N→ Prop,(c/2)*(l/2)≤ pr w P ∧
      (oneTonalMix (fun x=> oneMarkedDelta x (marks x)) (onW w P) ∨
        oneTonalTiny (fun x=> oneMarkedDelta x (marks x)) (onW w P) d)

end

end Lax793645.PhaseAlternative
