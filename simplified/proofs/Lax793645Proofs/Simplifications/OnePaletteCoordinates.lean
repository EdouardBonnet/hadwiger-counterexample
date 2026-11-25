import Lax793645Proofs.Simplifications.OneFullLinearPalettes
import Lax793645Proofs.Simplifications.FullLinearCoordinates
import Lax793645Proofs.Simplifications.OneJointPredictorCoordinates

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Function LinearMap Module Submodule Finset
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N R c : ℕ}

theorem one_star_key_surjective (l : Tag p.g) :
    Surjective (oneStarKey (p:=p) (N:=N) l) := by
  classical
  intro x
  refine ⟨fun e=>if h:inc e l then x ⟨e,h⟩ else 0,?_⟩
  funext e
  change (if h:inc e.val l then x ⟨e.val,h⟩ else 0)=x e
  simp only [dif_pos e.property]

/-- Store the rows of all unary partitions in one space of actual
ambient functionals. Its dimension is bounded by the sum of the row
budgets, even when neighboring tag keys repeat a component. -/
theorem one_palette_row_space (r : Tag p.g→ℕ) (hr : ∀ l,r l≤R)
    (L : ∀ l,OneAtomKey (p:=p) l N→ₗ[F]Vec (Fin (r l))) :
    ∃ H : Space (OneJointKey p N),dim H≤p.g*R ∧
      ∃ B : ∀ l,Module.Dual F H→ₗ[F]Vec (Fin (r l)),
        ∀ l x,L l (oneStarKey l x)=B l (oneJointCell H x) := by
  classical
  let row (l : Tag p.g) (j : Fin (r l)):=
    (LinearMap.proj j).comp ((L l).comp (oneStarKey (N:=N) l))
  choose v hv using fun l j=>one_key_pairing_surjective (row l j)
  let V : (Σ l,Fin (r l))→OneJointKey p N:=fun i=>v i.1 i.2
  let H:=Submodule.span F (Set.range V)
  have hdim : dim H≤p.g*R := by
    have hh:=finrank_range_le_card (R:=F) V
    have hb : (∑ l,r l)≤p.g*R := by
      calc
        _≤∑ _ : Tag p.g,R:=sum_le_sum (fun l _=>hr l)
        _=_:=by simp
    exact hh.trans (by simpa only [Fintype.card_sigma,Fintype.card_fin] using hb)
  have hmem (l : Tag p.g) (j : Fin (r l)) : v l j∈H:=subset_span ⟨⟨l,j⟩,rfl⟩
  let B (l : Tag p.g) : Module.Dual F H→ₗ[F]Vec (Fin (r l)):=
    LinearMap.pi (fun j=>Module.evalEquiv F H ⟨v l j,hmem l j⟩)
  refine ⟨H,hdim,B,?_⟩
  intro l x
  funext j
  change row l j x=oneKeyPairing x (v l j)
  rw [hv l j]
  exact one_key_pairing_symm _ _

/-- Full palette cells have onto coordinate maps and injective color
names. The same bounded ambient row space controls every tag and bit. -/
theorem one_full_palette_coordinates (Y : OneSilhouette p N c)
    (hY : OneFullLinearSilhouette Y R) :
    ∃ r : Tag p.g→ℕ,(∀ l,r l≤R) ∧
      ∃ L : ∀ l,OneAtomKey (p:=p) l N→ₗ[F]Vec (Fin (r l)),
      (∀ l,Surjective (L l)) ∧
      ∃ ι : ∀ l,F→Vec (Fin (r l))→Fin c,
      (∀ l q,Injective (ι l q)) ∧ (∀ l q x,Y l q x=ι l q (L l x)) ∧
      ∃ H : Space (OneJointKey p N),dim H≤p.g*R ∧
      ∃ B : ∀ l,Module.Dual F H→ₗ[F]Vec (Fin (r l)),
      (∀ l,Surjective (B l)) ∧
      ∀ l x,L l (oneStarKey l x)=B l (oneJointCell H x) := by
  classical
  choose r hr L hL ι hι he using fun l=>full_linear_coordinates (hY l)
  obtain ⟨H,hH,B,hB⟩:=one_palette_row_space r hr L
  refine ⟨r,hr,L,hL,ι,hι,he,H,hH,B,?_,hB⟩
  intro l z
  obtain ⟨x,hx⟩:=hL l z
  obtain ⟨y,hy⟩:=one_star_key_surjective l x
  exact ⟨oneJointCell H y,(hB l y).symm.trans (by rw [hy,hx])⟩

/-- The prepared mixed-law rank event makes every palette coordinate
map onto on the free input block. No full-rank assertion is made for an
arbitrary separately normalized leaf. -/
theorem one_palette_free_surjective (H : Space (OneJointKey p N))
    (l : Tag p.g) (L : OneAtomKey (p:=p) l N→ₗ[F]Vec (Fin R))
    (B : Module.Dual F H→ₗ[F]Vec (Fin R)) (hB : Surjective B)
    (he : ∀ x,L (oneStarKey l x)=B (oneJointCell H x))
    (J : Vec (Fin n)→ₗ[F]OneFull p n) (o : OneOrient p n N)
    (ho : Injective ((oneMixedRow J o).comp H.subtype)) :
    Surjective (L.comp ((oneStarKey l).comp (oneFreeKey J o))) := by
  intro c
  obtain ⟨z,hz⟩:=hB c
  obtain ⟨v,hv⟩:=one_joint_cell_free_surjective J o H ho z
  refine ⟨v,?_⟩
  change L (oneStarKey l (oneFreeKey J o v))=c
  rw [he]
  change B (((oneJointCell H).comp (oneFreeKey J o)) v)=c
  rw [hv,hz]

end
end Lax793645Proofs.Simplifications
