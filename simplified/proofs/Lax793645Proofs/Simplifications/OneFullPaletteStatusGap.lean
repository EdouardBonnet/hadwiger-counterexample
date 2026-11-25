import Lax793645Proofs.Simplifications.OnePaletteQueryCells
import Lax793645Proofs.Simplifications.OneFullCellReference
import Lax793645Proofs.Simplifications.OneTableSupportGap

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis OneAppearance Function LinearMap
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N r c d d' : ℕ}

/-- The support gap for an actual full palette follows from the raw
reference count and surjectivity on the free input block. All normalizing
and cell-nonemptiness hypotheses of the table theorem are discharged. -/
theorem one_full_palette_status_gap (hg : Odd p.g) (K : ℕ)
    (hd : d≤K^2) (hd' : d'≤K^2)
    (Y : OneSilhouette p N c) (l : Tag p.g) (q : F)
    (a b : Label p.b) (f f' : Flavor p.g)
    (hx : (⟨l,a,f,q⟩ : Appearance p).apt)
    (hy : (⟨l,b,f',q⟩ : Appearance p).apt)
    (hp : 1≤p.r) (hn : 2*p.r≤n)
    (i i' : Nodes) (o o' : OneUnit p n N) (m : Mixer p n)
    (v : Ax p n d) (v' : Ax p n d')
    (hv : ∀ j : Fin d,totalRank (v (Pi.single j 1))≤K)
    (hv' : ∀ j : Fin d',totalRank (v' (Pi.single j 1))≤K)
    (z : Magazine p d) (z' : Magazine p d')
    (hq : z.1.sumBit=q) (hq' : z'.1.sumBit=q)
    (L : OneAtomKey (p:=p) l N→ₗ[F]Vec (Fin r)) (hL : Surjective L)
    (ι : Vec (Fin r)→Fin c) (hι : Injective ι)
    (hY : ∀ k,Y l q k=ι (L k))
    (hfree : Surjective (onePaletteFree ⟨l,a,f,q⟩ (o i) L))
    (hfree' : Surjective (onePaletteFree ⟨l,b,f',q⟩ (o' i') L))
    (hN : bp (-(N:ℝ)/2)≤bp (-num (oneUnaryRail l))/2)
    (hsmall : 2*bp (num (oneUnaryRail l))*bp (-(N:ℝ)/2)≤bp (-(r:ℝ))/2) :
    let x : Appearance p:=⟨l,a,f,q⟩
    let y : Appearance p:=⟨l,b,f',q⟩
    let overlap:=avg (oneReference x Y) (fun j=>
      oneReflected x Y i o m v j z*oneReflected y Y i' o' m v' j z')
    overlap=0 ∨ bp (-(4*(oneStatusCoordinateBound p (K^2) K:ℝ)+1))≤overlap := by
  let x : Appearance p:=⟨l,a,f,q⟩
  let y : Appearance p:=⟨l,b,f',q⟩
  obtain ⟨S,hS,hne⟩:=one_palette_input_cells x (o i) L hfree hx hp hn
  obtain ⟨S',hS',hne'⟩:=one_palette_input_cells y (o' i') L hfree' hy hp hn
  let ν:=mapW (oneLawOmega p N l q) L
  have hν (k : Vec (Fin r)) : unif k/2≤ν k :=
    (one_full_cell_reference l q L hL hN hsmall k).1
  have href : oneReference x Y=mapW ν ι := by
    unfold oneReference ν
    rw [mapW_nested]
    congr 1
    exact funext hY
  have hcell (w : Knobs p.g n) : oneShowTag x Y (o i) w=
      ι (onePaletteInput x (o i) L w+L (oneFace x (o i) 0)) := by
    change Y l q (oneFace x (o i) w)=_
    exact (hY _).trans (congrArg ι (one_palette_input_affine x (o i) L w))
  have hcell' (w : Knobs p.g n) : oneShowTag y Y (o' i') w=
      ι (onePaletteInput y (o' i') L w+L (oneFace y (o' i') 0)) := by
    change Y l q (oneFace y (o' i') w)=_
    exact (hY _).trans (congrArg ι (one_palette_input_affine y (o' i') L w))
  exact one_table_support_gap hg K hd hd' Y x y i i' o o' m v v' hv hv'
    z z' hq hq' (onePaletteInput x (o i) L) (onePaletteInput y (o' i') L)
    (L (oneFace x (o i) 0)) (L (oneFace y (o' i') 0)) S S' hS hS'
    ι hι hcell hcell' hne hne' ν hν href

end
end Lax793645Proofs.Simplifications
