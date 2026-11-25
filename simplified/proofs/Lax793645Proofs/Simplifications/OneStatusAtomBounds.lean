import Lax793645Proofs.Simplifications.AffineStatusAtomBounds
import Lax793645Proofs.Simplifications.OneFullPaletteStatusGap

/-! Uniform atom bounds for the actual conditional status laws, including their fallback on empty cells. -/

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Function LinearMap Finset StatusAnalysis Filter
open scoped Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

theorem one_reflected_status_atom_bound {p : Shape} {n N d r R : ℕ}
    (hg : Odd p.g) (K : ℕ) (hd : d≤K^2)
    (Y : OneSilhouette p N r) (hY : OneFullLinearSilhouette Y R)
    (x : StatusAnalysis.Appearance p) (i : Nodes) (o : OneUnit p n N)
    (m : Mixer p n) (v : StatusAnalysis.Ax p n d)
    (hv : ∀ j : Fin d,totalRank (v (Pi.single j 1))≤K)
    (c : Fin r) (z : StatusAnalysis.Magazine p d)
    (hz : 0<OneAppearance.oneReflected x Y i o m v c z) :
    bp (-(oneStatusCoordinateBound p (K^2) K:ℝ))≤
      OneAppearance.oneReflected x Y i o m v c z := by
  open StatusAnalysis OneAppearance in
  by_cases hq : z.1.sumBit=x.q
  · obtain ⟨a,ha,L,hL⟩:=hY x.l
    have hcell (u w : Knobs p.g n) : oneShowTag x Y (o i) u=oneShowTag x Y (o i) w ↔
        onePaletteInput x (o i) L u=onePaletteInput x (o i) L w := by
      change Y x.l x.q (oneFace x (o i) u)=Y x.l x.q (oneFace x (o i) w) ↔ _
      rw [hL,one_palette_input_affine x (o i) L u,one_palette_input_affine x (o i) L w,
        add_right_cancel_iff]
    have hf:=one_status_coordinates_bounded hg i v m o x.l x.s x.f K hd hv
    have hw : x.wit n=unifOn (fun u=>(oneProfile x i o m v u).1.sumBit=z.1.sumBit) := by
      unfold Appearance.wit scopedBit spins
      rw [←draws_unif,on_unif,hq]
      rfl
    unfold oneReflected at hz ⊢
    change 0<pr (stained (x.wit n) (oneShowTag x Y (o i)) c)
      (fun u=>oneProfile x i o m v u=z) at hz
    change _≤pr (stained (x.wit n) (oneShowTag x Y (o i)) c)
      (fun u=>oneProfile x i o m v u=z)
    rw [hw] at hz ⊢
    exact stained_linear_status_gap (onePaletteInput x (o i) L)
      (oneShowTag x Y (o i)) hcell (oneProfile x i o m v)
      (oneStatusCoordinateBound p (K^2) K) hf (fun z=>z.1.sumBit) z c hz
  · have he : oneReflected x Y i o m v c z=0:=
      oneRefInk x Y i o m v c z (fun h=>hq h.2.1)
    rw [he] at hz
    exact (lt_irrefl _ hz).elim

end
end Lax793645Proofs.Simplifications
