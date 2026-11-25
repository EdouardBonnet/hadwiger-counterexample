import Lax793645Proofs.Simplifications.OneFiniteReferenceGap
import Lax793645Proofs.Simplifications.FullLinearCoordinates

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Function LinearMap Matrix Finset
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {N r : ℕ}

/-- The prescribed quadratic Gram law is within a fixed factor of the
uniform law on every full linear cell, once its linear bias is smaller
than half a cell. -/
theorem one_full_cell_reference (l : Tag p.g) (q : F)
    (L : OneAtomKey (p:=p) l N→ₗ[F]Vec (Fin r)) (hL : Surjective L)
    (hN : bp (-(N:ℝ)/2)≤bp (-num (oneUnaryRail l))/2)
    (hsmall : 2*bp (num (oneUnaryRail l))*bp (-(N:ℝ)/2)≤bp (-(r:ℝ))/2)
    (c : Vec (Fin r)) :
    unif c/2≤mapW (oneLawOmega p N l q) L c ∧
      mapW (oneLawOmega p N l q) L c≤2*unif c := by
  classical
  let E:=oneUnaryCoordinates l N
  let ν:=unifOn (gramKeySet (oneUnaryRail l) (fun _=>q) N)
  let P:=LinearMap.toMatrix' (L.comp E.toLinearMap)
  have hP (x : KeyCoordinates (TagStar l) N) : P*ᵥx=L (E x):=
    LinearMap.toMatrix'_mulVec _ x
  have hsur : Surjective P.mulVec := by
    intro y
    obtain ⟨x,hx⟩:=hL y
    exact ⟨E.symm x,(hP _).trans (by rw [E.apply_symm_apply,hx])⟩
  obtain ⟨hν,_,hbias⟩:=gram_reference_bias (oneUnaryRail l) (fun _=>q) hN
  have hh:=linear_cell_mass_error ν hν
    (2*bp (num (oneUnaryRail l))*bp (-(N:ℝ)/2))
    (mul_nonneg (mul_nonneg (by norm_num) (bp_pos _).le) (bp_pos _).le) hbias P c
  have he : mapW ν P.mulVec=mapW (oneLawOmega p N l q) L := by
    rw [show ν=mapW (oneLawOmega p N l q) E.symm from
      (one_unary_reference_coordinates l q).symm,mapW_nested]
    congr 1
    funext x
    change P*ᵥ(E.symm x)=L x
    rw [hP,E.apply_symm_apply]
  have hpUnif : mapW (unif : Wgt (KeyCoordinates (TagStar l) N)) P.mulVec=unif :=
    map_unif_surjective P.mulVecLin hsur
  rw [he,hpUnif] at hh
  have hu : (unif c:ℝ)=bp (-(r:ℝ)) := by
    rw [unif_apply,card_space,dim_vec,Fintype.card_fin,bp_neg]
  rw [←hu] at hsmall
  have hlo:=neg_le_abs (mapW (oneLawOmega p N l q) L c-unif c)
  have hhi:=le_abs_self (mapW (oneLawOmega p N l q) L c-unif c)
  have hpos:0≤(unif c:ℝ):=unif_law.nz c
  constructor <;> linarith only [hh,hsmall,hlo,hhi,hpos]

end
end Lax793645Proofs.Simplifications
