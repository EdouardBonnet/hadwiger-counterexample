import Lax793645Proofs.Simplifications.OnePredictorLabelExtension
import Lax793645Proofs.Simplifications.ExactSupportPredictions

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Function LinearMap Submodule
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- An exact prediction on affine cells is a quadratic polynomial plus
a constant multiple of the tester. The proof uses sections and a second
difference, with no approximation or agreement threshold. -/
theorem affine_cell_prediction_exact (A : Vec J→ₗ[F]Vec I) (k : Vec I)
    (S : Vec I→ₗ[F]Vec J) (hS : ∀ c,A (S c)=c)
    (q R : Vec J→F) (hR : R∈Stocks J 2)
    (hqS : ∀ x c,q (x+S c)=q x) (φ : F→Vec I→F)
    (hq : Surjective q) (a b : Vec J)
    (hqdiff : ∀ y,q (y+a+b)-q (y+a)-q (y+b)+q y=1)
    (he : ∀ x,R x=φ (q x) (A x+k)) :
    ∃ (Q : Vec I→F) (γ : F),Q∈Stocks I 2 ∧
      (∀ d c,φ d c=Q c+γ*d) ∧
      (∀ x,R x=Q (A x+k)+γ*q x) ∧
      ∃ y,q y=0 ∧ Q=(fun c=>R (affineRecenter A k S y c)) := by
  let R' := fun x=>R (recenteredInput A k S x)
  have hR' : R'∈Stocks (I⊕J) 2 := polynomial_affine_substitution 2 R hR
    (recenteredInput A k S) (recentered_input_affine A k S)
  have he' (c : Vec I) (y : Vec J) : R' (joinCoordinates (c,y))=φ (q y) c := by
    change R (y+S (c-(A y+k)))=φ (q y) c
    rw [he,hqS,map_add,hS]
    congr 1
    abel
  obtain ⟨Q,γ,hQ,hφ,y,hy,hslice⟩:=exact_quadratic_predictor R' hR' q φ hq a b hqdiff he'
  exact ⟨Q,γ,hQ,hφ,fun x=>(he x).trans (hφ _ _),y,hy,hslice⟩

variable {p : Shape} {n N r : ℕ}

/-- The exact normal form for the construction's actual keys. Its
section uses only the free coordinates, so the later rank bound is
independent of the number of cell coordinates. -/
theorem one_affine_cell_exact (l : Tag p.g) (A : OneAtomKey (p:=p) l N→ₗ[F]Vec (Fin r))
    (o : OneOrient p n N) (s : Label p.b) (f : Flavor p.g)
    (hfree : Surjective (A.comp ((oneStarKey l).comp (oneFreeKey (oneFreeColumns p n s) o))))
    (w : Pdual p n) (φ : F→Vec (Fin r)→F)
    (hr : 1≤p.r) (hn : 2*p.r≤n)
    (he : ∀ x,w (useAtom p l s f x)=
      φ (dialed p l f x) (A (oneAtomKeyValue o l s (lit f l x)))) :
    ∃ (Q : Vec (Fin r)→F) (γ : F),Q∈Stocks (Fin r) 2 ∧
      (∀ d c,φ d c=Q c+γ*d) ∧
      (∀ x,w (useAtom p l s f x)=Q (A (oneAtomKeyValue o l s (lit f l x)))+γ*dialed p l f x) ∧
      ∃ (y : Knobs p.g n) (S : Vec (Fin r)→ₗ[F]Vec (Fin n)),
        Q=(fun c=>w (useAtom p l s f (y+freeKnob p n (S c)))) := by
  let B:=A.comp ((oneStarKey l).comp (oneFreeKey (oneFreeColumns p n s) o))
  obtain ⟨S,hS⟩:=B.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hfree)
  let S':=(flatFree p n).comp S
  have hS' (c : Vec (Fin r)) : oneLocalCells A o s f (S' c)=c := by
    change oneLocalCells A o s f (flatFree p n (S c))=c
    rw [one_local_cell_free]
    exact LinearMap.congr_fun hS c
  let q:=fun x : Base p.g n=>dialed p l f (flattenKnobs p n x)
  let R:=fun x : Base p.g n=>w (useAtom p l s f (flattenKnobs p n x))
  have hqS (x : Base p.g n) (c : Vec (Fin r)) : q (x+S' c)=q x :=
    flat_tester_free l f x (S c)
  have hq : Surjective q := by
    intro b
    obtain ⟨z,hz,_⟩:=exists_of_pr_pos (spins_law p n).nz
      ((by norm_num : (0:ℝ)<1/4).trans_le (dialed_bit_mass l f hr hn b))
    exact ⟨(flattenKnobs p n).symm z,by simpa only [q,LinearEquiv.apply_symm_apply] using hz⟩
  obtain ⟨a,b,hab⟩:=dialed_tester_directions l s f hr hn
  have he' (x : Base p.g n) : R x=φ (q x) (oneLocalCells A o s f x+oneLocalOffset A o s f) := by
    rw [←one_local_cell_affine]
    exact he _
  obtain ⟨Q,γ,hQ,hφ,hval,y,_,hy⟩:=affine_cell_prediction_exact (oneLocalCells A o s f)
    (oneLocalOffset A o s f) S' hS' q R (one_input_functional_quadratic w l s f)
    hqS φ hq a b hab he'
  refine ⟨Q,γ,hQ,hφ,?_,?_,S,?_⟩
  · intro x
    simpa only [R,q,←one_local_cell_affine,LinearEquiv.apply_symm_apply]
      using hval ((flattenKnobs p n).symm x)
  · exact flattenKnobs p n y-freeKnob p n (S (oneLocalCells A o s f y+oneLocalOffset A o s f))
  · rw [hy]
    funext c
    change w (useAtom p l s f (flattenKnobs p n
      (y+S' (c-(oneLocalCells A o s f y+oneLocalOffset A o s f)))))=
      w (useAtom p l s f ((flattenKnobs p n y-
        freeKnob p n (S (oneLocalCells A o s f y+oneLocalOffset A o s f)))+
          freeKnob p n (S c)))
    apply congrArg (fun z=>w (useAtom p l s f z))
    rw [map_add]
    change flattenKnobs p n y+freeKnob p n
      (S (c-(oneLocalCells A o s f y+oneLocalOffset A o s f)))=_
    rw [map_sub,map_sub]
    abel

variable {T : Type}

/-- Exact support identities give common quadratic polynomials for the
whole population. The only continuation step concerns the excluded
selector labels. -/
theorem one_common_quadratic_exact (r : Tag p.g→ℕ)
    (A : ∀ l,OneAtomKey (p:=p) l N→ₗ[F]Vec (Fin (r l)))
    (φ : ∀ l,F→Vec (Fin (r l))→F) (P : T→Prop)
    (o : T→OneOrient p n N) (w : T→Pdual p n) (E : T→Finset (Label p.b))
    (hP : ∃ t,P t) (hr : 1≤p.r) (hn : 2*p.r≤n)
    (hE : ∀ t,P t→((E t).card:ℝ)<bp ((p.b:ℝ)-2*p.j))
    (hfree : ∀ t,P t→∀ s,s∉E t→∀ l,
      Surjective ((A l).comp ((oneStarKey l).comp (oneFreeKey (oneFreeColumns p n s) (o t)))))
    (he : ∀ t,P t→∀ s,s∉E t→∀ l f x,w t (useAtom p l s f x)=
      φ l (dialed p l f x) (A l (oneAtomKeyValue (o t) l s (lit f l x)))) :
    ∃ (Q : ∀ l,Vec (Fin (r l))→F) (γ : Tag p.g→F),
      (∀ l,Q l∈Stocks (Fin (r l)) 2) ∧
      (∀ l d c,φ l d c=Q l c+γ l*d) ∧
      (∀ t,P t→∀ l s f x,w t (useAtom p l s f x)=
        Q l (A l (oneAtomKeyValue (o t) l s (lit f l x)))+γ l*dialed p l f x) ∧
      ∃ t,P t ∧ ∀ l,∃ (s : Label p.b) (y : Knobs p.g n)
        (S : Vec (Fin (r l))→ₗ[F]Vec (Fin n)),
          Q l=(fun c=>w t (useAtom p l s Flavor.full (y+freeKnob p n (S c)))) := by
  classical
  obtain ⟨t0,ht0⟩:=hP
  have hcard : (E t0).card<Fintype.card (Label p.b) := by
    have hb := (hE t0 ht0).trans_le (bp_le (show (p.b:ℝ)-2*p.j≤p.b by
      have hh : 0≤(p.j:ℝ):=Nat.cast_nonneg _
      linarith only [hh]))
    have hc : bp (p.b:ℝ)=(Fintype.card (Label p.b):ℝ) := by
      simp [Label,F,bp_nat,ZMod.card]
    rw [hc] at hb
    exact_mod_cast hb
  obtain ⟨s0,hs0⟩ : ∃ s,s∉E t0 := by
    by_contra! hh
    have hc:=Finset.card_le_card (show Finset.univ⊆E t0 from fun s _=>hh s)
    rw [Finset.card_univ] at hc
    omega
  choose Q γ hQ hφ hv hslice using fun l=>one_affine_cell_exact l (A l) (o t0) s0 Flavor.full
    (hfree t0 ht0 s0 hs0 l) (w t0) (φ l) hr hn (he t0 ht0 s0 hs0 l Flavor.full)
  refine ⟨Q,γ,hQ,hφ,?_,t0,ht0,fun l=>⟨s0,hslice l⟩⟩
  intro t ht l s f x
  apply one_predictor_label_extension l (A l) (o t) (w t) (Q l) (hQ l) (γ l) (E t) (hE t ht) f x
  intro u hu
  exact (he t ht u hu l f x).trans (hφ l _ _)

end
end Lax793645Proofs.Simplifications
