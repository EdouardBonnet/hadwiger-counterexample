import Lax793645Proofs.Simplifications.AffineCellPrediction
import Lax793645Proofs.Simplifications.TesterPolynomialInputs

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open LinearMap Function Submodule
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
variable {p : Shape} {n N r : ℕ}
variable {l : Tag p.g}

def oneLocalCells (A : OneAtomKey (p:=p) l N→ₗ[F]Vec (Fin r))
    (o : OneOrient p n N) (s : Label p.b) (f : Flavor p.g) :
    Base p.g n→ₗ[F]Vec (Fin r) :=
  A.comp ((oneStarKey l).comp ((onePrimalKey o).comp (flatSpring l s f)))

def oneLocalOffset (A : OneAtomKey (p:=p) l N→ₗ[F]Vec (Fin r))
    (o : OneOrient p n N) (s : Label p.b) (f : Flavor p.g) : Vec (Fin r) :=
  A (oneAtomKeyValue o l s (lit f l 0))

theorem one_local_cell_affine (A : OneAtomKey (p:=p) l N→ₗ[F]Vec (Fin r))
    (o : OneOrient p n N) (s : Label p.b) (f : Flavor p.g) (x : Base p.g n) :
    A (oneAtomKeyValue o l s (lit f l (flattenKnobs p n x)))=
      oneLocalCells A o s f x+oneLocalOffset A o s f := by
  change A (oneStarKey l (onePrimalKey o (spring p l s f (flattenKnobs p n x))))=_
  rw [flat_spring_affine,map_add,map_add,map_add]
  rfl

theorem one_local_cell_free (A : OneAtomKey (p:=p) l N→ₗ[F]Vec (Fin r))
    (o : OneOrient p n N) (s : Label p.b) (f : Flavor p.g) (z : Vec (Fin n)) :
    oneLocalCells A o s f (flatFree p n z)=
      A (oneStarKey l (oneFreeKey (oneFreeColumns p n s) o z)) := by
  change A (oneStarKey l (onePrimalKey o (spring p l s f (freeKnob p n z)-spring p l s f 0)))=_
  have hh:=spring_add_free l s f (0:Knobs p.g n) z
  rw [zero_add] at hh
  rw [hh,add_sub_cancel_left]
  rfl

/-- The fixed-error polynomial fit applies to the construction's actual
keys. The hypothesis is surjectivity on the free coordinates, supplied
outside exponentially small prepared mixed mass. -/
theorem one_affine_cell_fit (l : Tag p.g) (A : OneAtomKey (p:=p) l N→ₗ[F]Vec (Fin r))
    (o : OneOrient p n N) (s : Label p.b) (f : Flavor p.g)
    (hfree : Surjective (A.comp ((oneStarKey l).comp (oneFreeKey (oneFreeColumns p n s) o))))
    (w : Pdual p n) (φ : F→Vec (Fin r)→F)
    (hr : 1≤p.r) (hn : 2*p.r≤n) (ε : ℝ) (hε : 5*ε<1/16)
    (he : pr (spins p n) (fun x=>
      φ (dialed p l f x) (A (oneAtomKeyValue o l s (lit f l x)))≠w (useAtom p l s f x))≤ε) :
    ∃ (Q : Vec (Fin r)→F) (γ : F),Q∈Stocks (Fin r) 2 ∧
      (∀ x,w (useAtom p l s f x)=Q (A (oneAtomKeyValue o l s (lit f l x)))+γ*dialed p l f x) ∧
      (∀ d : F,pr unif (fun c=>φ d c≠Q c+γ*d)≤4*ε) ∧
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
  have hqbit (b : F) : (1/4:ℝ)≤pr unif (fun x=>q x=b) := by
    rw [←mapW_pr unif (flattenKnobs p n) (fun x=>dialed p l f x=b),flatten_knobs_uniform]
    exact dialed_bit_mass l f hr hn b
  obtain ⟨a,b,hab⟩:=dialed_tester_directions l s f hr hn
  have he' : pr unif (fun x=>φ (q x) (oneLocalCells A o s f x+oneLocalOffset A o s f)≠R x)≤ε := by
    simp_rw [←one_local_cell_affine]
    rw [←mapW_pr unif (flattenKnobs p n) (fun x=>φ (dialed p l f x)
      (A (oneAtomKeyValue o l s (lit f l x)))≠w (useAtom p l s f x)),flatten_knobs_uniform]
    exact he
  obtain ⟨Q,γ,hQ,hval,hfit,y,hy⟩:=affine_cell_prediction_fit (oneLocalCells A o s f)
    (oneLocalOffset A o s f) S' hS' q R (one_input_tester_quadratic l s f)
    (one_input_functional_quadratic w l s f) hqS φ a b hqbit hab ε hε he'
  refine ⟨Q,γ,hQ,?_,hfit,?_,S,?_⟩
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

theorem one_affine_cell_transfer (l : Tag p.g) (A : OneAtomKey (p:=p) l N→ₗ[F]Vec (Fin r))
    (o : OneOrient p n N) (s : Label p.b) (f : Flavor p.g)
    (hfree : Surjective (A.comp ((oneStarKey l).comp (oneFreeKey (oneFreeColumns p n s) o))))
    (w : Pdual p n) (φ : F→Vec (Fin r)→F)
    (Q : Vec (Fin r)→F) (hQ : Q∈Stocks (Fin r) 2) (γ : F)
    (ε : ℝ) (hε : 5*ε<1/4)
    (hfit : ∀ d : F,pr unif (fun c=>φ d c≠Q c+γ*d)≤4*ε)
    (he : pr (spins p n) (fun x=>
      φ (dialed p l f x) (A (oneAtomKeyValue o l s (lit f l x)))≠w (useAtom p l s f x))≤ε) :
    ∀ x,w (useAtom p l s f x)=Q (A (oneAtomKeyValue o l s (lit f l x)))+γ*dialed p l f x := by
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
  have he' : pr unif (fun x=>φ (q x) (oneLocalCells A o s f x+oneLocalOffset A o s f)≠R x)≤ε := by
    simp_rw [←one_local_cell_affine]
    rw [←mapW_pr unif (flattenKnobs p n) (fun x=>φ (dialed p l f x)
      (A (oneAtomKeyValue o l s (lit f l x)))≠w (useAtom p l s f x)),flatten_knobs_uniform]
    exact he
  have hv:=affine_cell_prediction_transfer (oneLocalCells A o s f) (oneLocalOffset A o s f)
    S' hS' q R (one_input_tester_quadratic l s f) (one_input_functional_quadratic w l s f)
    hqS φ Q hQ γ ε hε hfit he'
  intro x
  simpa only [R,q,←one_local_cell_affine,LinearEquiv.apply_symm_apply]
    using hv ((flattenKnobs p n).symm x)

end
end Lax793645Proofs.Simplifications
