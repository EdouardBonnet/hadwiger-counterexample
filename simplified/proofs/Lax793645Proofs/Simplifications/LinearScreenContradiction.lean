import Lax793645Proofs.Simplifications.LinearScreenSlopes

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix Function LinearMap Finset Module
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {p : Shape} {n N : ℕ}

theorem shared_dial_tested (l : Tag p.g) (x : Knobs p.g n) :
    dialed p l Flavor.sharedOnly x=tested p.r (x Block.S) := by
  simp [dialed,Digest.sumBit,Digest.diagO,scan,Flavor.keeps,asBlock,Block.S]

theorem shared_dial_mass (l : Tag p.g) (hr : 1≤p.r) (hn : 2*p.r≤n) (b : F) :
    (1/4:ℝ)≤pr (spins p n) (fun x=>dialed p l Flavor.sharedOnly x=b) := by
  classical
  have he:=prodW_pr_inj (e:=fun _ : Unit=>Block.S (g:=p.g))
    (fun _ _ _=>Subsingleton.elim _ _) (fun _=>unif_law (α:=Vec (Fin n)))
    (fun _ x=>tested p.r x=b)
  simp only [forall_const,Fintype.prod_unique] at he
  simp_rw [shared_dial_tested]
  change (1/4:ℝ)≤pr (prodW (fun _ : Block p.g=>unif)) _
  rw [he]
  exact tested_fraction p.r n hr hn b

/-- The pointwise contradiction has a fixed positive error threshold.
It needs full rank only at this endpoint, before restricting any pair event. -/
theorem linear_screen_gap (H : Space (PairedKeys (Comp p.g) (Fin N)))
    [Fintype (Module.Dual F H)] (o : Orient p n N) (s : Label p.b)
    (hfree : Injective ((mixedFrameRowLinear (selectorFreeColumns p n s) o).comp H.subtype))
    (g : Augur p N) (φ : Tag p.g→F→Module.Dual F H→F)
    (hφ : ∀ l q x,g l q (starKey l x)=φ l q (jointCell H x))
    (E : Finset (Tag p.g)) (r : ℕ) (ε : ℝ) (m : Mixer p n)
    (hj : 1≤p.j) (hr : 1≤p.r) (hg : Odd p.g) (hn : 2*p.r≤n)
    (hroom : 2*r+1≤privateWidth p.g*(p.g-E.card)*p.r)
    (hscreen : screen p o s E r g ε) :
    1≤(p.g:ℝ)*(fiddleRate p (Hue (2*r+1))+4)*ε := by
  classical
  have hpos : 0<p.g:=by obtain ⟨k,hk⟩:=hg; omega
  let l0 : Tag p.g:=⟨0,hpos⟩
  let f:=Flavor.sharedOnly (g:=p.g)
  let q0:=dialed p l0 f (n:=n)
  let c0:=queryCell H o l0 s f
  let ν:=mapW (spins p n) q0
  have hν : IsLaw ν:=mapW_law (spins_law p n) q0
  have hq (b : F) : (1/4:ℝ)≤pr ν (fun q=>q=b) := by
    rw [mapW_pr]
    exact shared_dial_mass l0 hr hn b
  have hflow : flowZ p (spins p n) := by
    intro x z
    rw [spins,←draws_unif]
    rfl
  have hqflow (x : Knobs p.g n) (z : Vec (Fin n)) : q0 (update x Block.Z z)=q0 x := by
    unfold q0 dialed
    rw [scannedZ]
  have hjoint : mapW (spins p n) (fun x=>(q0 x,c0 x))=pairW ν unif :=
    joint_key_independence H o s hfree l0 f (spins p n) hflow q0 hqflow
  have hsave:=hscreen
  obtain ⟨w,hw,_⟩:=hsave
  have hbad (x : Knobs p.g n) (hx : (∑ l,φ l (q0 x) (c0 x))≠0) :
      ∃ l,mismatch p g w l s f o x := by
    by_contra! hh
    apply hx
    have he (l : Tag p.g) : φ l (q0 x) (c0 x)=w (atom p l s (lit f l0 x)) := by
      have hp:=Eq.symm (not_ne_iff.mp (hh l))
      change g l (dialed p l f x) (keyOne p l s (lit f l x) o)=w (useAtom p l s f x) at hp
      rw [←common_dial p l0 l x,←common_lit p l0 l x] at hp
      change _=w (atom p l s (lit f l x)) at hp
      rw [←common_lit p l0 l x] at hp
      rw [←star_primal_key o l s (lit f l0 x),hφ] at hp
      exact hp
    simp_rw [he,←map_sum,atom_union,map_zero]
  have hp : pr (spins p n) (fun x=>(∑ l,φ l (q0 x) (c0 x))≠0)≤(p.g:ℝ)*ε := by
    refine ((pr_mono (spins_law p n).nz hbad).trans (pr_exists_le (spins_law p n).nz _)).trans ?_
    exact (Finset.sum_le_sum (fun l _=>hw l f)).trans_eq (by
      simp only [Finset.sum_const,card_univ,Tag,Fintype.card_fin,nsmul_eq_mul])
  have hp' : pr (pairW unif ν) (fun x : Module.Dual F H×F=>(∑ l,φ l x.2 x.1)≠0)
      ≤(p.g:ℝ)*ε := by
    have he:=mapW_pr (spins p n) (fun x=>(q0 x,c0 x))
      (fun x : F×Module.Dual F H=>(∑ l,φ l x.1 x.2)≠0)
    rw [hjoint] at he
    rw [←he] at hp
    rw [pr,pairW_avg,avg_avg]
    simpa only [pr,pairW_avg] using hp
  have hs (l : Tag p.g) : pr unif (fun c=>cellSlope (φ l) c=0)≤
      fiddleRate p (Hue (2*r+1))*ε :=
    linear_screen_slopes H o s hfree g φ hφ E r ε m hj hn hroom hscreen l
  have ht:=odd_cell_parity (unif : Wgt (Module.Dual F H)) unif_law ν hν
    (_root_.id : F→F) (1/4) (by norm_num) hq φ
    (by simpa only [Tag,Fintype.card_fin] using hg)
  have hb:=Finset.sum_le_sum fun l (_ : l∈univ)=>hs l
  simp only [Finset.sum_const,card_univ,Tag,Fintype.card_fin,nsmul_eq_mul] at hb
  have hh:=ht.trans hp'
  nlinarith only [hh,hb]

end
end Lax793645Proofs.Simplifications
