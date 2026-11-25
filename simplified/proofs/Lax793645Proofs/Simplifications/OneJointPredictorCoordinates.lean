import Lax793645Proofs.Simplifications.OnePreparedLinearRank
import Lax793645Proofs.Simplifications.LinearCellCoordinates

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open LinearMap Module Function Finset Submodule
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N : ℕ}

abbrev OneJointKey (p : Shape) (N : ℕ):=Comp p.g→Vec (HyperbolicIdx N)
abbrev OneAtomKey (l : Tag p.g) (N : ℕ):=TagStar l→Vec (HyperbolicIdx N)
abbrev OneAugur (p : Shape) (N : ℕ):=∀ l : Tag p.g,F→OneAtomKey l N→F
def OneLinearAugur (g : OneAugur p N) (R : ℕ):=∀ l,HasLinearCells (g l) R

def oneKeyPairing : LinearMap.BilinForm F (OneJointKey p N):=
  ∑ e,(hyperbolicMatrix N).toQuadraticForm'.polarBilin.compl₁₂
    (LinearMap.proj e) (LinearMap.proj e)

theorem one_key_pairing_apply (x y : OneJointKey p N) :
    oneKeyPairing x y=∑ e,(hyperbolicMatrix N).toQuadraticForm'.polarBilin (x e) (y e) := by
  simp only [oneKeyPairing,LinearMap.sum_apply,LinearMap.compl₁₂_apply,LinearMap.proj_apply]

theorem one_key_pairing_symm (x y : OneJointKey p N) : oneKeyPairing x y=oneKeyPairing y x := by
  simp only [one_key_pairing_apply,binary_polar_symm (hyperbolicMatrix N).toQuadraticForm']

theorem one_key_pairing_nondegenerate : (oneKeyPairing (p:=p) (N:=N)).Nondegenerate := by
  have hleft (x : OneJointKey p N) (h : ∀ y,oneKeyPairing x y=0) : x=0 := by
    funext e
    apply (hyperbolic_matrix_nondegenerate N).1
    intro z
    have hh:=h (Pi.single e z)
    simpa only [one_key_pairing_apply,Pi.single_apply,apply_ite,map_zero,
      Finset.sum_ite_eq',mem_univ,if_true] using hh
  exact ⟨hleft,fun x h=>hleft x (fun y=>(one_key_pairing_symm x y).trans (h y))⟩

theorem one_key_pairing_surjective (f : Module.Dual F (OneJointKey p N)) :
    ∃ v,f=oneKeyPairing v := by
  obtain ⟨v,hv⟩:=(oneKeyPairing.toDual one_key_pairing_nondegenerate).surjective f
  exact ⟨v,hv.symm⟩

def oneJointCell (H : Space (OneJointKey p N)) :
    OneJointKey p N→ₗ[F]Module.Dual F H:=H.subtype.dualMap.comp oneKeyPairing

def oneFreeKey (J : Vec (Fin n)→ₗ[F]OneFull p n) (o : OneOrient p n N) :
    Vec (Fin n)→ₗ[F]OneJointKey p N:=LinearMap.pi (fun e=>(o e).comp J)

theorem one_free_pairing (J : Vec (Fin n)→ₗ[F]OneFull p n) (o : OneOrient p n N)
    (v : OneJointKey p N) (z : Vec (Fin n)) :
    oneKeyPairing v (oneFreeKey J o z)=oneMixedRow J o v z := by
  simp only [one_key_pairing_apply,oneFreeKey,oneMixedRow,quadraticPolarRead,
    LinearMap.sum_apply,LinearMap.comp_apply,LinearMap.pi_apply,LinearMap.proj_apply,
    LinearMap.dualMap_apply]

theorem one_joint_cell_free_surjective (J : Vec (Fin n)→ₗ[F]OneFull p n)
    (o : OneOrient p n N) (H : Space (OneJointKey p N))
    (h : Injective ((oneMixedRow J o).comp H.subtype)) :
    Surjective ((oneJointCell H).comp (oneFreeKey J o)) := by
  intro c
  obtain ⟨f,hf⟩:=LinearMap.dualMap_surjective_of_injective h c
  obtain ⟨z,hz⟩:=(Module.evalEquiv F (Vec (Fin n))).surjective f
  refine ⟨z,?_⟩
  apply LinearMap.ext
  intro v
  change oneKeyPairing (oneFreeKey J o z) v.val=c v
  rw [one_key_pairing_symm,one_free_pairing]
  have hh:=LinearMap.congr_fun hf v
  rw [←hz] at hh
  exact hh

def oneStarKey (l : Tag p.g) : OneJointKey p N→ₗ[F]OneAtomKey l N:=
  LinearMap.pi (fun e=>LinearMap.proj e.val)

/-- The shared coordinate space is the span of actual functionals on
one physical vector per component. Repeated star coordinates add no rank. -/
theorem one_joint_predictor_coordinates (g : OneAugur p N) (R : ℕ)
    (hg : OneLinearAugur g R) :
    ∃ H : Space (OneJointKey p N),dim H≤p.g*R ∧
      ∃ φ : Tag p.g→F→Module.Dual F H→F,
        ∀ l q x,g l q (oneStarKey l x)=φ l q (oneJointCell H x) := by
  choose A φ hφ using fun l=>linear_cells_exact (hg l)
  let L (l : Tag p.g) (j : Fin R):=
    (LinearMap.proj j).comp ((A l).comp (oneStarKey (N:=N) l))
  choose v hv using fun l j=>one_key_pairing_surjective (L l j)
  let V : Tag p.g×Fin R→OneJointKey p N:=fun i=>v i.1 i.2
  let H:=Submodule.span F (Set.range V)
  have hdim : dim H≤p.g*R := by
    have hh:=finrank_range_le_card (R:=F) V
    simpa only [Set.finrank,H,dim,Fintype.card_prod,Fintype.card_fin] using hh
  have hmem (l : Tag p.g) (j : Fin R) : v l j∈H:=Submodule.subset_span ⟨(l,j),rfl⟩
  refine ⟨H,hdim,fun l q c=>φ l q (fun j=>c ⟨v l j,hmem l j⟩),?_⟩
  intro l q x
  rw [hφ l q (oneStarKey l x)]
  congr 1
  funext j
  change L l j x=oneKeyPairing x (v l j)
  rw [hv l j]
  exact one_key_pairing_symm _ _

end
end Lax793645Proofs.Simplifications
