/-
Adapted from OpenAI, openai/math, commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (Apache-2.0).
Original module: OAI.Combinatorics.HadwigerCounterexample.GramArrayConcentration.
Changes: archive package namespace and imports; see references/upstream-construction.json.
-/
import Lax793645Proofs.Simplifications.AffineSliceVariance

namespace Lax793645Proofs.Upstream.OAI

/-! # Gram Array Concentration -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Module LinearMap Function Filter
open scoped BigOperators Topology
variable {p : Shape} {I : Type} [Fintype I] [DecidableEq I] {n N : ℕ}
def magazine (p : Shape) (l : Tag p.g) (s : Label p.b) (f : Flavor p.g)
    (P : Display p I N→Prop) (a : I→ Tickets p) (o : Orient p n N) :=
  pr (sketchLaw p n a) (fun i => P (drill p (incision p l s f i) o))

set_option maxHeartbeats 1000000 in
theorem magazine_var (p : Shape) (l : Tag p.g) (s : Label p.b) (f : Flavor p.g)
    (P : Display p I N → Prop) (a : I → Tickets p) (m : Mixer p n)
    (h : 2*num (Full p n)<N) (hj : 1≤p.j) (hn : 2*p.r≤n) (hN : 2*num I-(N:ℝ)≤ -1)
    (k : ℝ) (hk : num (Bool × Comp p.g × I)≤ k) (hK : 2*k-N≤ -1) :
    let g:= tied (drStage p I) Bool
    let V := displayLaw p I N (labGram p l f a)
    avg (raw m N) (fun i => (magazine p l s f P a i - pr V P)^2) ≤
      2 * netFact g * twinkle g k N + 3*bp (num Bool*num I - n) := by
  exact Lax793645Proofs.Simplifications.slice_variance_from_query
    p l s f P a m h hj hn hN k hk hK

end HadwigerCounterexample

end

end Lax793645Proofs.Upstream.OAI
