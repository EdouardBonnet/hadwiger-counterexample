import Lax793645Proofs.Simplifications.OneZeroDiscrepancyPrediction
import Lax793645Proofs.Simplifications.OnePolynomialInputs
import Lax793645Proofs.Simplifications.QuadraticCoordinateBound

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix Function LinearMap
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
variable {p : Shape} {n N r : ℕ}

theorem one_yoke_free_matrix (m : Mixer p n) (x : OneUnit p n N) (i : Bool)
    (u : Profile p n) (α : F) (K : ℕ) (hk : totalRank u≤K) (hg : Odd p.g)
    (l : Tag p.g) (s : Label p.b) (f : Flavor p.g) (y : Knobs p.g n) :
    ∃ M : Moment p n,M.rank≤oneScreenRank p K ∧
      ∃ c : F,∀ z : Vec (Fin n),
        oneYoke m x i u α (useAtom p l s f (y+freeKnob p n z))=
          evmat M (spring p l s f (y+freeKnob p n z))
            (spring p l s f (y+freeKnob p n z))+c := by
  obtain ⟨M,hM,ht⟩:=one_inner_gem x i l
  let V:=M+qmix m u l
  have hV : V.rank≤oneScreenRank p K := by
    refine (mrk_add_le ..).trans ((Nat.add_le_add hM (qmix_rank ..)).trans ?_)
    unfold oneScreenRank
    change _+p.J*(tagDegree p.g)*(2*totalRank u)≤_
    exact (Nat.add_le_add_left (Nat.mul_le_mul_left (p.J*(tagDegree p.g))
      (Nat.mul_le_mul_left 2 hk)) _).trans_eq (by ring)
  refine ⟨V,hV,T0 p n u (useAtom p l s f y)+α*role p n (useAtom p l s f y),?_⟩
  intro z
  have he : y+freeKnob p n z=update y Block.Z (y Block.Z+z) := by
    classical
    funext B
    by_cases hB : B=Block.Z <;> simp [freeKnob,hB]
  have hcore : T0 p n u (useAtom p l s f (y+freeKnob p n z))=
      T0 p n u (useAtom p l s f y) := by rw [he,T0_scanZ p hg]
  have hrole : role p n (useAtom p l s f (y+freeKnob p n z))=
      role p n (useAtom p l s f y) := by
    rw [he,role_scan,role_scan,scannedZ]
  change oneInner x i (useAtom p l s f (y+freeKnob p n z))+
    (T0 p n u (useAtom p l s f (y+freeKnob p n z))+
      Tmix m u (useAtom p l s f (y+freeKnob p n z))+
      α*role p n (useAtom p l s f (y+freeKnob p n z)))=_
  rw [hcore,hrole,show oneInner x i (useAtom p l s f (y+freeKnob p n z))=
    mpair M (mom p s (lit f l (y+freeKnob p n z))) from ht s _,
    show Tmix m u (useAtom p l s f (y+freeKnob p n z))=
      mpair (qmix m u l) (mom p s (lit f l (y+freeKnob p n z))) from Tmix_atom ..]
  rw [←mpair_outer]
  dsimp only [V]
  rw [mpair_add]
  change mpair M (mom p s (lit f l (y+freeKnob p n z)))+
    (T0 p n u (useAtom p l s f y)+
      mpair (qmix m u l) (mom p s (lit f l (y+freeKnob p n z)))+
        α*role p n (useAtom p l s f y))=
    (mpair M (mom p s (lit f l (y+freeKnob p n z)))+
      mpair (qmix m u l) (mom p s (lit f l (y+freeKnob p n z))))+
        (T0 p n u (useAtom p l s f y)+α*role p n (useAtom p l s f y))
  abel

/-- The fitted predictor uses at most twice the screen rank many
linear coordinates, regardless of its original coordinate budget. -/
theorem one_yoke_section_coordinates (m : Mixer p n) (x : OneUnit p n N) (i : Bool)
    (u : Profile p n) (α : F) (K : ℕ) (hk : totalRank u≤K) (hg : Odd p.g)
    (l : Tag p.g) (s : Label p.b) (f : Flavor p.g) (y : Knobs p.g n)
    (S : Vec (Fin r)→ₗ[F]Vec (Fin n)) :
    HasLinearCells (fun (_ : F) c=>oneYoke m x i u α
      (useAtom p l s f (y+freeKnob p n (S c)))) (2*oneScreenRank p K) := by
  obtain ⟨M,hM,c,hc⟩:=one_yoke_free_matrix m x i u α K hk hg l s f y
  let P:=(blockRay p n s Block.Z).mulVecLin.comp S
  have he (v : Vec (Fin r)) : spring p l s f (y+freeKnob p n (S v))=
      P v+spring p l s f y := by
    rw [spring_add_free,add_comm]
    rfl
  simpa only [hc,he] using affine_matrix_linear_cells (Q:=F) M P
    (spring p l s f y) c (oneScreenRank p K) hM

end
end Lax793645Proofs.Simplifications
