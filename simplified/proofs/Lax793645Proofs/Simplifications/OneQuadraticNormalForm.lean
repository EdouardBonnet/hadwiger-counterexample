import Lax793645Proofs.Simplifications.OneFittedCoordinateBound
import Lax793645Proofs.Simplifications.OnePredictorRowSpace
import Lax793645Proofs.Simplifications.OneExactSlopes

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Function LinearMap
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
variable {p : Shape} {n N : ℕ}

/-- The tester argument removes the displayed tester slope at one
endpoint, without needing a prediction at the other endpoint. -/
theorem one_quadratic_endpoint_slopes (H : Space (OneJointKey p N))
    (x : OneUnit p n N) (i : Bool) (u : Profile p n) (α : F) (m : Mixer p n)
    (K : ℕ) (hk : totalRank u≤K) (r : Tag p.g→ℕ)
    (A : ∀ l,OneAtomKey (p:=p) l N→ₗ[F]Vec (Fin (r l)))
    (Q : ∀ l,Vec (Fin (r l))→F) (γ : Tag p.g→F)
    (hjoint : ∀ s,Injective ((oneMixedRow (oneFreeColumns p n s) (x i)).comp H.subtype))
    (hfactor : ∀ l a b,oneJointCell H a=oneJointCell H b→
      A l (oneStarKey l a)=A l (oneStarKey l b))
    (hg : Odd p.g) (h3 : 3≤p.g) (hj : 1≤p.j) (hr : 1≤p.r) (hn : 2*p.r≤n)
    (hroom : 4*oneScreenRank p K<p.g*p.r)
    (hval : ∀ l s f y,oneYoke m x i u α (useAtom p l s f y)=
      Q l (A l (oneAtomKeyValue (x i) l s (lit f l y)))+γ l*dialed p l f y) :
    (∀ l,γ l=0) ∧ (bitSupport (testerCoefficients u α)).card*p.r≤2*oneScreenRank p K := by
  let J:=oneFreeKey (oneFreeColumns p n (0:Label p.b)) (x i)
  let C:=(oneJointCell H).comp J
  have hsur : Surjective C:=one_joint_cell_free_surjective _ _ H
    (hjoint 0)
  obtain ⟨S,hS⟩:=C.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hsur)
  let ψ (l : Tag p.g) (c : Module.Dual F H):=Q l (A l (oneStarKey l (J (S c))))
  have hψ (l : Tag p.g) (a : OneJointKey p N) :
      Q l (A l (oneStarKey l a))=ψ l (oneJointCell H a) := by
    apply congrArg (Q l)
    apply hfactor l
    exact (LinearMap.congr_fun hS (oneJointCell H a)).symm
  apply one_exact_slopes_zero H x i u α m K
    hk 0 (hjoint 0) ψ γ hg h3 hj hr hn hroom
  intro l f y
  rw [hval]
  change Q l (A l (oneStarKey l (onePrimalKey (x i) (spring p l 0 f y))))+_=_
  rw [hψ]
  rfl

/-- Once common quadratic forms are given, tester ranks and the shared
atom identity remove the tester slope. This step does not depend on how
the common forms were obtained. -/
theorem one_quadratic_population_of_forms (m : Mixer p n) (P : OneUnit p n N→Prop)
    (u : OneUnit p n N→Bool→Profile p n) (α : Bool→F)
    (r : Bool→Tag p.g→ℕ)
    (A : ∀ i l,OneAtomKey (p:=p) l N→ₗ[F]Vec (Fin (r i l)))
    (K : ℕ) (hk : ∀ x,P x→∀ i,totalRank (u x i)≤K)
    (hg : Odd p.g) (h3 : 3≤p.g) (hj : 1≤p.j)
    (hr : 1≤p.r) (hn : 2*p.r≤n) (hroom : 4*oneScreenRank p K<p.g*p.r)
    (H : Bool→Space (OneJointKey p N))
    (hfactor : ∀ i l a b,oneJointCell (H i) a=oneJointCell (H i) b→
      A i l (oneStarKey l a)=A i l (oneStarKey l b))
    (hjoint : ∀ x,P x→∀ i s,
      Injective ((oneMixedRow (oneFreeColumns p n s) (x i)).comp (H i).subtype))
    (Q : ∀ i l,Vec (Fin (r i l))→F) (γ : Bool→Tag p.g→F)
    (hQ : ∀ i l,Q i l∈Stocks (Fin (r i l)) 2)
    (hval : ∀ i x,P x→∀ l s f y,oneYoke m x i (u x i) (α i) (useAtom p l s f y)=
      Q i l (A i l (oneAtomKeyValue (x i) l s (lit f l y)))+γ i l*dialed p l f y)
    (hs : ∀ i,∃ x,P x ∧ ∀ l,∃ (s : Label p.b) (y : Knobs p.g n)
      (S : Vec (Fin (r i l))→ₗ[F]Vec (Fin n)),
        Q i l=(fun c=>oneYoke m x i (u x i) (α i)
          (useAtom p l s Flavor.full (y+freeKnob p n (S c))))) :
    ∃ g' : Bool→OneAugur p N,
      (∀ i,OneLinearAugur (g' i) (2*oneScreenRank p K)) ∧
      (∀ x,P x→ oneClaimed x g' m (u x) α (fun _=>∅) 0) ∧
      (∀ x,P x→∀ i,(bitSupport (testerCoefficients (u x i) (α i))).card*p.r≤
        2*oneScreenRank p K) ∧
      (∀ i l,γ i l=0) ∧
      ∀ i l q x,g' i l q x=Q i l (A i l x) := by
  classical
  choose x0 hx0 hslice using hs
  have hunit (x : OneUnit p n N) (hx : P x) (i : Bool) :
      (∀ l,γ i l=0) ∧ (bitSupport (testerCoefficients (u x i) (α i))).card*p.r≤
        2*oneScreenRank p K :=
    one_quadratic_endpoint_slopes (H i) x i (u x i) (α i) m K (hk x hx i)
      (r i) (A i) (Q i) (γ i) (hjoint x hx i) (hfactor i) hg h3 hj hr hn hroom
      (hval i x hx)
  have hzero (i : Bool) : ∀ l,γ i l=0 := (hunit (x0 i) (hx0 i) i).1
  let g' : Bool→OneAugur p N:=fun i l _ x=>Q i l (A i l x)
  refine ⟨g',?_,?_,fun x hx i=>(hunit x hx i).2,hzero,fun _ _ _ _=>rfl⟩
  · intro i l
    obtain ⟨s,y,S,hs⟩:=hslice i l
    have hc : HasLinearCells (fun (_ : F) c=>Q i l c) (2*oneScreenRank p K) := by
      rw [hs]
      exact one_yoke_section_coordinates m (x0 i) i (u (x0 i) i) (α i) K
        (hk (x0 i) (hx0 i) i) hg l s Flavor.full y S
    exact linear_cells_precompose hc (A i l)
  · intro x hx i s _ l f
    have hz : oneMismatch (g' i) (oneYoke m x i (u x i) (α i)) l s f (x i)=fun _=>False := by
      funext y
      apply propext
      change (oneYoke m x i (u x i) (α i) (useAtom p l s f y)≠
        Q i l (A i l (oneAtomKeyValue (x i) l s (lit f l y))))↔False
      rw [hval i x hx l s f y,hzero i l,zero_mul,add_zero]
      simp
    rw [hz,pr_false]

end
end Lax793645Proofs.Simplifications
