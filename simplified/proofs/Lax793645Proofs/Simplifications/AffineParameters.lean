import Lax793645Proofs.Simplifications.AffineScalarOptions
import Lax793645Proofs.Simplifications.AffinePairedCollisionBounds

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis Filter
open scoped Topology

/-- Parameter conditions for the affine route. The selector degree is one;
the former interpolation room is replaced by a fixed label-deletion budget. -/
structure AffineAnalyticParameters (p : Shape) (M : ℕ) (b : PreparationParameters)
    (r : ℕ) : Prop extends QueryParameters p M b r where
  affine : p.j=1
  reserve : 10*affineScalarBudget p b.pins+1000 ≤ b.B
  secure : ∀ᶠ n : ℕ in atTop,AffineOptions.earnsScore p n (M*n) b.pins (2*b.ζ)

instance {p : Shape} {M : ℕ} {b : PreparationParameters} {r : ℕ} :
    Coe (AffineAnalyticParameters p M b r) (QueryParameters p M b r) :=
  ⟨AffineAnalyticParameters.toQueryParameters⟩

end Lax793645Proofs.Simplifications
