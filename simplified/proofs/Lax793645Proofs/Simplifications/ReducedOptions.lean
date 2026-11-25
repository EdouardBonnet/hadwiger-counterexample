import Lax793645Proofs.Simplifications.ReducedBinaryPrescriptions
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.PairedOptions

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis
noncomputable section
variable {p : Shape} {q : Format} {d e : Rates}

/-- Scalar compatibility of the deterministic expansion of the smaller
binary prescription. All other status and flag conditions are unchanged. -/
def onePermission (w : Typus p q d e) : Prop :=
  (∀ i,1≤q i ∧q i≤7) ∧w.qA.moral w.t w.z ∧w.qB.moral w.t w.z ∧
  (∀ i,fullq w.z i=1) ∧rhyme w.qA.amp w.qB.amp ∧
  proclaims p w.qA.amp w.qB.amp w.t (reducedScript w.qA.script) ∧
  proclaims p w.qB.amp w.qA.amp w.t (reducedScript w.qB.script)

end
end Lax793645Proofs.Simplifications
