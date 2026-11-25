import Lax793645.ConnectedMatching
import Lax793645.CliqueMinor

/-!
---
title: Clique minors from connected matchings
type: theorem
---
Every finite graph satisfies $3h(G)\le |V(G)|+4\mathrm{cm}(G)+2$.
This is Proposition 3.5 of the source paper, written with integer coefficients.
-/

namespace Lax793645.MatchingMinorBound

open ConnectedMatching CliqueMinor

axiom hadwiger_matching_bound {V : Type} [Fintype V] (G : SimpleGraph V) :
    3 * hadwigerNumber G ≤ Fintype.card V + 4 * connectedMatchingNumber G + 2

end Lax793645.MatchingMinorBound
