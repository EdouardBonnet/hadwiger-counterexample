import Lax793645Proofs.Simplifications.OneConditionalStatusGap
import Lax793645Proofs.Simplifications.OneSurrogateStatusLaws
import Lax793645Proofs.Simplifications.FullCellStatusTables

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis OneAppearance Function LinearMap
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N r d d' : ℕ}
variable {C : Type} [AddCommGroup C] [Module F C] [Fintype C]

/-- The positive gap holds for the finite tables already used by
scalar duality. The hypotheses expose the full-cell coordinates and
the prepared good-frame event; no replacement table is introduced. -/
theorem one_table_support_gap (hg : Odd p.g) (K : ℕ)
    (hd : d≤K^2) (hd' : d'≤K^2)
    (Y : OneSilhouette p N r) (x y : Appearance p)
    (i i' : Nodes) (o o' : OneUnit p n N) (m : Mixer p n)
    (v : Ax p n d) (v' : Ax p n d')
    (hv : ∀ j : Fin d,totalRank (v (Pi.single j 1))≤K)
    (hv' : ∀ j : Fin d',totalRank (v' (Pi.single j 1))≤K)
    (z : Magazine p d) (z' : Magazine p d')
    (hq : z.1.sumBit=x.q) (hq' : z'.1.sumBit=y.q)
    (L L' : Knobs p.g n→ₗ[F]C) (k k' : C)
    (S S' : C→ₗ[F]Knobs p.g n)
    (hS : ∀ c,L (S c)=c) (hS' : ∀ c,L' (S' c)=c)
    (ι : C→Fin r) (hι : Injective ι)
    (hcell : ∀ a,oneShowTag x Y (o i) a=ι (L a+k))
    (hcell' : ∀ a,oneShowTag y Y (o' i') a=ι (L' a+k'))
    (hne : ∀ c,∃ a,dialed p x.l x.f a=x.q ∧ L a+k=c)
    (hne' : ∀ c,∃ a,dialed p y.l y.f a=y.q ∧ L' a+k'=c)
    (ν : Wgt C) (hν : ∀ c,unif c/2≤ν c)
    (href : oneReference x Y=mapW ν ι) :
    let overlap:=avg (oneReference x Y) (fun a=>
      oneReflected x Y i o m v a z*oneReflected y Y i' o' m v' a z')
    overlap=0 ∨ bp (-(4*(oneStatusCoordinateBound p (K^2) K:ℝ)+1))≤overlap := by
  have hf:=one_status_coordinates_bounded hg i v m o x.l x.s x.f K hd hv
  have hf':=one_status_coordinates_bounded hg i' v' m o' y.l y.s y.f K hd' hv'
  have hc : ∀ c,∃ a,
      (oneSpecify p i v m o x.l x.s x.f a).1.sumBit=z.1.sumBit ∧ L a+k=c := by
    simpa only [hq,oneSpecify,dialed] using hne
  have hc' : ∀ c,∃ a,
      (oneSpecify p i' v' m o' y.l y.s y.f a).1.sumBit=z'.1.sumBit ∧ L' a+k'=c := by
    simpa only [hq',oneSpecify,dialed] using hne'
  have hh:=full_cell_status_overlap_gap L L' k k' S S' hS hS'
    (oneSpecify p i v m o x.l x.s x.f) (oneSpecify p i' v' m o' y.l y.s y.f)
    (oneStatusCoordinateBound p (K^2) K) hf hf'
    (fun z:Magazine p d=>z.1.sumBit) (fun z:Magazine p d'=>z.1.sumBit)
    z z' ι hι hc hc' ν hν
  have hwx : x.wit n=unifOn (fun a=>
      (oneSpecify p i v m o x.l x.s x.f a).1.sumBit=z.1.sumBit) := by
    unfold Appearance.wit scopedBit spins
    rw [←draws_unif,on_unif,hq]
    rfl
  have hwy : y.wit n=unifOn (fun a=>
      (oneSpecify p i' v' m o' y.l y.s y.f a).1.sumBit=z'.1.sumBit) := by
    unfold Appearance.wit scopedBit spins
    rw [←draws_unif,on_unif,hq']
    rfl
  dsimp only at hh ⊢
  rw [href]
  unfold oneReflected
  have hprof : oneProfile x i o m v=oneSpecify p i v m o x.l x.s x.f := rfl
  have hprof' : oneProfile y i' o' m v'=oneSpecify p i' v' m o' y.l y.s y.f := rfl
  rw [hprof,hprof',hwx,hwy]
  simp_rw [show oneShowTag x Y (o i)=(fun a=>ι (L a+k)) from funext hcell,
    show oneShowTag y Y (o' i')=(fun a=>ι (L' a+k')) from funext hcell']
  exact hh

end
end Lax793645Proofs.Simplifications
