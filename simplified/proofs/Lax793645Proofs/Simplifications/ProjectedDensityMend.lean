import Lax793645Proofs.Simplifications.BoundedOverlapTransfer
import Lax793645Proofs.Simplifications.OneSidedOverlap

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
noncomputable section
variable {A B : Type} [Fintype A] [Fintype B]

/-- Direct finite mending through actual common projections. No tail
estimate is needed once their overlap has been bounded directly. -/
theorem projected_density_mend (ν : Wgt A) (hν : IsLaw ν) (P : A→B)
    (f g p q : Wgt A) (hf : bower f) (hg : bower g)
    (hp : ∀ x,0≤p x) (hq : ∀ x,0≤q x) (hps : lsupp p ν) (hqs : lsupp q ν) :
    dip ν f g^2≤dip ν (banner ν P (density ν p)) (banner ν P (density ν q))+
      (varOne (mapW (fun x=>ν x*f x) P) (mapW p P)+
        varOne (mapW (fun x=>ν x*g x) P) (mapW q P)) := by
  have hh:=one_sided_projected_mend ν hν P f g (density ν p) (density ν q) hf hg
    (fun x=>div_nonneg (hp x) (hν.nz x)) (fun x=>div_nonneg (hq x) (hν.nz x))
  have he (u v : Wgt A):avg ν (fun x=>max (u x-v x) 0)≤lcost ν u v:=
    avg_mono hν.nz (fun x=>max_le (le_abs_self _) (abs_nonneg _))
  have h₁:=(he (banner ν P f) (banner ν P (density ν p))).trans
    (density_error ν P hν f p hps)
  have h₂:=(he (banner ν P g) (banner ν P (density ν q))).trans
    (density_error ν P hν g q hqs)
  linarith only [hh,h₁,h₂]

end
end Lax793645Proofs.Simplifications
