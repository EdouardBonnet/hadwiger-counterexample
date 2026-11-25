import Lax793645Proofs.Simplifications.OnePositiveOptions
import Lax793645Proofs.Simplifications.OneLinearPreparation

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open PreparationParameters StatusAnalysis Filter
open scoped Topology
noncomputable section

structure OneAnalyticParameters (p:Shape) (M:ℕ) (q:PreparationParameters) (s0:ℕ):Prop where
  planted:OnePlanted q p M
  unary:OneUnaryParameters p M (onePreparationPins q) s0
  thickness:4≤M
  affine:p.j=1
  jump:1≤p.J
  reserve:10*oneScalarBudget p (onePreparationPins q)+1000≤q.B
  spare:3*q.B<Fintype.card (Label p.b)
  exactLateRoom:4*oneScreenRank p (onePreparationPins q)<p.g*p.r
  secure:∀ᶠ n:ℕ in atTop,OneEarnsScore p n (M*n) (onePreparationPins q) (2*q.ζ)

def oneConflicted {p:Shape} {n N:ℕ} (m:Mixer p n) (w:Wgt (OneUnit p n N)):=
  pr (pairW w w) (oneClash m)<bp (-200*(2*N:ℝ))

structure OneVeil (p:Shape) (M:ℕ) (q:PreparationParameters) (s0:ℕ)
    (l:Filter ℕ) (m:cycleM p) (s:OneRhythms p M) (w:OneTale p M):Prop where
  parameters:OneAnalyticParameters p M q s0
  time:l≤atTop
  durable:OneDurable q l m w s
  moment:∀ᶠ n in l,OneNascent q (m n) (w n) ∧
    unaryGood (m n) (onePreparationPins q) s0 ∧ reducedBinaryGood (m n) ∧ oneConflicted (m n) (w n)

abbrev OneStations (p:Shape) (M K:ℕ) (s:OneRhythms p M):=
  ∀ n:ℕ,OneStation p n (M*n) K (s n)

theorem one_beam_cost (p:Shape) (N:ℕ):
    oneBeamPrice p N*bp (-200*(2*N:ℝ))≤bp (-(2*N:ℝ)) := by
  have hd:oneMaxSlots p≤56:=by
    unfold oneMaxSlots tagDegree CycleGeometry.degree
    have h:=min_le_left 2 (p.g-1)
    omega
  have hd':(oneMaxSlots p:ℝ)≤56:=by exact_mod_cast hd
  unfold oneBeamPrice
  rw [←bp_add]
  apply bp_le
  nlinarith only [hd',Nat.cast_nonneg (α:=ℝ) N]

end
end Lax793645Proofs.Simplifications
