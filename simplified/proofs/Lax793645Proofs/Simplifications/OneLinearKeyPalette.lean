import Lax793645Proofs.Simplifications.OneLinearPredictorCertificates
import Lax793645Proofs.Simplifications.OneKeyReferenceLaws

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open LinearMap Module Function Finset
open scoped Classical BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {N R r s : ℕ} {I T : Type} [Fintype I] [DecidableEq I]

def OneRefines (Y : OneSilhouette p N r) (X : OneSilhouette p N s):=
  ∀ l q,∃ f : Fin r→Fin s,∀ x,X l q x=f (Y l q x)
theorem one_refines_self (Y : OneSilhouette p N r) : OneRefines Y Y:=
  fun _ _=>⟨fun x=>x,fun _=>rfl⟩
theorem one_refines_trans {u : ℕ} {Y : OneSilhouette p N r} {X : OneSilhouette p N s}
    {Z : OneSilhouette p N u} (h : OneRefines Y X) (h' : OneRefines X Z) : OneRefines Y Z := by
  intro l q
  obtain ⟨f,hf⟩:=h l q
  obtain ⟨g,hg⟩:=h' l q
  exact ⟨g∘f,fun x=>by rw [hg,hf]; rfl⟩
theorem one_bundle_refines [Fintype T] [DecidableEq T]
    (f : T→ℕ) (Y : ∀ t,OneSilhouette p N (f t)) (t : T) :
    OneRefines (oneBundleY f Y) (Y t) := by
  intro l q
  let E:=Fintype.equivFin (∀ t,Fin (f t))
  exact ⟨fun c=>E.symm c t,fun x=>(congrFun (E.symm_apply_apply (fun t=>Y t l q x)) t).symm⟩
theorem one_duo_refines (Y : OneSilhouette p N r) (X : OneSilhouette p N s) :
    OneRefines (oneDuoY Y X) Y ∧OneRefines (oneDuoY Y X) X := by
  constructor
  · intro l q
    exact ⟨fun c=>(finProdFinEquiv.symm c).1,fun x=>(congrArg Prod.fst
      (finProdFinEquiv.symm_apply_apply (Y l q x,X l q x))).symm⟩
  · intro l q
    exact ⟨fun c=>(finProdFinEquiv.symm c).2,fun x=>(congrArg Prod.snd
      (finProdFinEquiv.symm_apply_apply (Y l q x,X l q x))).symm⟩

def oneKeyCoordinatesMap (t : Tagging p I) (N : ℕ) :
    OneKeys t N→ₗ[F]KeyCoordinates (KeySlots p t) N where
  toFun:=(oneQueryCoordinateEquiv t N).symm
  map_add' x y:=by funext ⟨u,b,i⟩; cases b <;> rfl
  map_smul' c x:=by funext ⟨u,b,i⟩; cases b <;> rfl

def oneKeySingle (t : Tagging p I) (i : I) : OneAtomKey (p:=p) (t i) N→ₗ[F]OneKeys t N where
  toFun:=fun x=>Pi.single (M:=fun j=>OneAtomKey (p:=p) (t j) N) i x
  map_add' x y:=by exact Pi.single_add (f:=fun j=>OneAtomKey (p:=p) (t j) N) i x y
  map_smul' c x:=by exact Pi.single_smul (f:=fun j=>OneAtomKey (p:=p) (t j) N) i c x

abbrev oneLinearPaletteSize (I : Type) [Fintype I] [DecidableEq I] (R : ℕ):=Fintype.card (I→Vec (Fin R))
def oneLinearKeyPalette (t : Tagging p I) (L : OneKeys t N→ₗ[F]Vec (Fin R)) :
    OneSilhouette p N (oneLinearPaletteSize I R):=fun l _ x=>
  Fintype.equivFin (I→Vec (Fin R)) (fun i=>if h:t i=l then L (Pi.single i (h ▸ x)) else 0)

theorem one_linear_key_palette_certificate (t : Tagging p I)
    (L : OneKeys t N→ₗ[F]Vec (Fin R)) :
    OneLinearSilhouette (oneLinearKeyPalette t L) (Fintype.card I*R) := by
  intro l
  let H (i : I) (_ : F) (x : OneAtomKey (p:=p) l N):=
    if h:t i=l then L (Pi.single i (h ▸ x)) else 0
  have hi (i : I) : HasLinearCells (H i) R := by
    by_cases h : t i=l
    · subst l
      refine ⟨R,le_rfl,L.comp (oneKeySingle t i),fun _ y=>y,?_⟩
      intro q x
      simp only [H,dif_pos rfl]
      rfl
    · have hc:=linear_cells_mono
        (linear_cells_constant (V:=OneAtomKey (p:=p) l N) (fun _ : F=>(0 : Vec (Fin R)))) (Nat.zero_le R)
      simpa only [H,dif_neg h] using hc
  have hh:=linear_cells_postprocess (linear_cells_bundle (fun _ : I=>R) H hi)
    (fun _ x=>Fintype.equivFin (I→Vec (Fin R)) x)
  convert hh using 1
  · rfl
  · simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul]

theorem one_linear_key_palette_read (t : Tagging p I)
    (L : OneKeys t N→ₗ[F]Vec (Fin R)) (i : I) (q : F) (x : OneAtomKey (p:=p) (t i) N) :
    (Fintype.equivFin (I→Vec (Fin R))).symm (oneLinearKeyPalette t L (t i) q x) i=
      L (Pi.single i x) := by
  simp [oneLinearKeyPalette]

/-- Recording the linear values directly needs only |I|R coordinates.
Every test on the whole tuple then has an exact finite product expansion. -/
theorem one_linear_cell_expansion (t : Tagging p I) (z : I→F)
    (L : OneKeys t N→ₗ[F]Vec (Fin R)) (Y : OneSilhouette p N r)
    (hY : OneRefines Y (oneLinearKeyPalette t L)) :
    ∃ U : (I→Vec (Fin R))→I→Fin r→ℝ,(∀ a i c,|U a i c|≤1) ∧
      ∀ (φ : Wgt (Vec (Fin R))) (x : OneKeys t N),
        φ (L x)=∑ a : I→Vec (Fin R),φ (∑ i,a i)*∏ i,U a i (Y (t i) (z i) (x i)) := by
  choose f hf using fun i=>hY (t i) (z i)
  let E:=Fintype.equivFin (I→Vec (Fin R))
  let U (a : I→Vec (Fin R)) (i : I) (c : Fin r):=ind (E.symm (f i c) i=a i)
  refine ⟨U,fun a i c=>by dsimp only [U]; rw [abs_of_nonneg (ind_nonneg _)]; exact ind_le_one _,?_⟩
  intro φ x
  let a (i : I):=L (Pi.single i (x i))
  have he : ∑ i,a i=L x := by
    dsimp only [a]
    rw [←map_sum,Finset.univ_sum_single]
  have hr (i : I) : E.symm (f i (Y (t i) (z i) (x i))) i=a i := by
    rw [←hf i (x i)]
    exact one_linear_key_palette_read t L i (z i) (x i)
  have hh (c : I→Vec (Fin R)) : (∏ i,U c i (Y (t i) (z i) (x i)))=ind (a=c) := by
    simp only [U,hr,←ind_all,←funext_iff]
  simp_rw [hh]
  rw [Finset.sum_eq_single a]
  · rw [ind_one rfl,mul_one,he]
  · intro c _ hc
    rw [ind_zero (Ne.symm hc),mul_zero]
  · simp

end
end Lax793645Proofs.Simplifications
