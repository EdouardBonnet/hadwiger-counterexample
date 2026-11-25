import Lax793645Proofs.Simplifications.OneJointPredictorCoordinates
import Lax793645Proofs.Simplifications.IndependentPredictorCoordinates

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open LinearMap Function Submodule Module Finset
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
variable {p : Shape} {n N : ℕ}

theorem one_star_key_surjective (l : Tag p.g) : Surjective (oneStarKey (N:=N) l) := by
  classical
  intro x
  let y : OneJointKey p N:=fun e=>if h : inc e l then x ⟨e,h⟩ else 0
  refine ⟨y,?_⟩
  funext e
  change (if h : inc e.val l then x ⟨e.val,h⟩ else 0)=x e
  rw [dif_pos e.property]

/-- Store the actual coordinate rows, including their dependence across
tag stars. Full rank of this one space supplies every local affine fit. -/
theorem one_predictor_row_space (r : Tag p.g→ℕ)
    (A : ∀ l,OneAtomKey (p:=p) l N→ₗ[F]Vec (Fin (r l)))
    (hA : ∀ l,Surjective (A l)) :
    ∃ H : Space (OneJointKey p N),dim H≤∑ l,r l ∧
      (∀ l x y,oneJointCell H x=oneJointCell H y→A l (oneStarKey l x)=A l (oneStarKey l y)) ∧
      ∀ (o : OneOrient p n N) (s : Label p.b),
        Injective ((oneMixedRow (oneFreeColumns p n s) o).comp H.subtype)→
        ∀ l,Surjective ((A l).comp ((oneStarKey l).comp (oneFreeKey (oneFreeColumns p n s) o))) := by
  classical
  let L (l : Tag p.g) (j : Fin (r l)):=
    (LinearMap.proj j).comp ((A l).comp (oneStarKey (N:=N) l))
  choose v hv using fun l j=>one_key_pairing_surjective (L l j)
  let V : (Σ l,Fin (r l))→OneJointKey p N:=fun i=>v i.1 i.2
  let H:=Submodule.span F (Set.range V)
  have hdim : dim H≤∑ l,r l := by
    have hh:=finrank_range_le_card (R:=F) V
    simpa only [Set.finrank,H,dim,Fintype.card_sigma,Fintype.card_fin] using hh
  have hmem (l : Tag p.g) (j : Fin (r l)) : v l j∈H:=Submodule.subset_span ⟨⟨l,j⟩,rfl⟩
  have hfactor (l : Tag p.g) (x y : OneJointKey p N)
      (hxy : oneJointCell H x=oneJointCell H y) : A l (oneStarKey l x)=A l (oneStarKey l y) := by
    funext j
    have hh:=LinearMap.congr_fun hxy ⟨v l j,hmem l j⟩
    change oneKeyPairing x (v l j)=oneKeyPairing y (v l j) at hh
    change L l j x=L l j y
    rw [hv l j]
    simpa only [one_key_pairing_symm] using hh
  refine ⟨H,hdim,hfactor,?_⟩
  intro o s ho l c
  obtain ⟨x,hx⟩:=(hA l).comp (one_star_key_surjective l) c
  obtain ⟨z,hz⟩:=one_joint_cell_free_surjective (oneFreeColumns p n s) o H ho (oneJointCell H x)
  refine ⟨z,?_⟩
  exact (hfactor l _ x hz).trans hx

/-- The exception is bounded in the prepared marginal before any leaf
normalization or compatible-pair restriction. -/
theorem one_prepared_coordinate_rank (m : Mixer p n)
    (hroom : Fintype.card (Row p n)+2*p.h+1≤N) (hN : 4≤N)
    (r : Tag p.g→ℕ) (A : ∀ l,OneAtomKey (p:=p) l N→ₗ[F]Vec (Fin (r l)))
    (hA : ∀ l,Surjective (A l)) (ρ : Wgt (OneOrient p n N)) (hρ₀ : ∀ o,0≤ρ o)
    (hρ : ∀ o,ρ o≤bp ((n:ℝ)/32)*oneRaw m N o) :
    pr ρ (fun o=>∃ s l,¬Surjective ((A l).comp ((oneStarKey l).comp
      (oneFreeKey (oneFreeColumns p n s) o))))≤8*bp ((∑ l,r l:ℕ)+p.b-31*(n:ℝ)/32) := by
  obtain ⟨H,hH,_,hfree⟩:=one_predictor_row_space r A hA
  have hsub (o : OneOrient p n N)
      (h : ∃ s l,¬Surjective ((A l).comp ((oneStarKey l).comp
        (oneFreeKey (oneFreeColumns p n s) o)))) :
      ∃ s,¬Injective ((oneMixedRow (oneFreeColumns p n s) o).comp H.subtype) := by
    obtain ⟨s,l,hs⟩:=h
    exact ⟨s,fun hi=>hs (hfree o s hi l)⟩
  refine ((pr_mono hρ₀ hsub).trans (one_prepared_linear_rank m hroom hN H ρ hρ)).trans ?_
  have hh : (dim H:ℝ)≤(∑ l,r l:ℕ) := by exact_mod_cast hH
  exact mul_le_mul_of_nonneg_left (bp_le (by linarith only [hh])) (by norm_num)

end
end Lax793645Proofs.Simplifications
