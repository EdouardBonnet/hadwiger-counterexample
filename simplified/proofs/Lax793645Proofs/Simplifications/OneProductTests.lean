import Lax793645Proofs.Simplifications.OneLinearKeyPalette

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis Filter Finset Function
open scoped Classical BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p:Shape} {N r s:ℕ} {I J:Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

structure OnePaint (t:Tagging p I) (N:ℕ) where
  coeff:ℝ
  flies:∀ i,OneAtomKey (p:=p) (t i) N→Prop

def oneMural {t:Tagging p I} (F:J→OnePaint t N):Wgt (OneKeys t N):=
  fun x=>∑ j,(F j).coeff*∏ i,ind ((F j).flies i (x i))
def OneDesign (t:Tagging p I) (W:Wgt (OneKeys t N)) (k:ℕ):Prop:=
  ∃ F:Fin k→OnePaint t N,W=oneMural F ∧ ∀ j,|(F j).coeff|≤1

def OnePigments {t:Tagging p I} (z:I→F) (Y:OneSilhouette p N r) (w:OnePaint t N):=
  ∀ i,∃ g:Fin r→Bool,∀ x,w.flies i x ↔ g (Y (t i) (z i) x)=true

abbrev onePaletteSize (I J:Type) [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]:=Fintype.card (J×I→Bool)

theorem one_build_palette (t:Tagging p I) (z:I→F) (w:J→OnePaint t N):
    ∃ Y:OneSilhouette p N (onePaletteSize I J),∀ j,OnePigments z Y (w j) := by
  let E:=Fintype.equivFin (J×I→Bool)
  let H (l) (x:OneAtomKey (p:=p) l N) (j:J) (i:I):=
    if h:t i=l then decide ((w j).flies i (h ▸ x)) else false
  let Y:OneSilhouette p N (onePaletteSize I J):=fun l _ x=>E (fun a=>H l x a.1 a.2)
  refine ⟨Y,fun j i=>⟨fun c=>E.symm c (j,i),fun x=>?_⟩⟩
  change _ ↔ E.symm (E (fun a=>H (t i) x a.1 a.2)) (j,i)=true
  rw [Equiv.symm_apply_apply]
  simp [H]

theorem one_finer_pigment {t:Tagging p I} {z:I→F} {Y:OneSilhouette p N r}
    {X:OneSilhouette p N s} (h:OneRefines Y X) (w:OnePaint t N)
    (hw:OnePigments z X w):OnePigments z Y w := by
  intro i
  obtain ⟨g,hg⟩:=hw i
  obtain ⟨f,hf⟩:=h (t i) (z i)
  exact ⟨g ∘ f,fun x=>(hg x).trans (by rw [hf]; rfl)⟩

theorem one_unary_product_design (t:Tagging p I)
    (P:∀ i,OneAtomKey (p:=p) (t i) N→Prop):
    OneDesign t (fun x=>ind (∀ i,P i (x i))) 1 := by
  refine ⟨fun _=>⟨1,P⟩,funext fun x=>?_,fun _=>by norm_num⟩
  simp only [oneMural,Fin.sum_univ_one,one_mul,ind_all]

theorem one_design_mul_one (t:Tagging p I) (f g:Wgt (OneKeys t N))
    (k:ℕ) (hf:OneDesign t f k) (hg:OneDesign t g 1):
    OneDesign t (fun x=>f x*g x) k := by
  obtain ⟨A,hA,hAc⟩:=hf
  obtain ⟨B,hB,hBc⟩:=hg
  let H (j:Fin k):OnePaint t N:=
    ⟨(A j).coeff*(B 0).coeff,fun i x=>(A j).flies i x ∧ (B 0).flies i x⟩
  refine ⟨H,funext fun x=>?_,fun j=>?_⟩
  · rw [hA,hB]
    simp only [oneMural,Fin.sum_univ_one]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    simp only [H,ind_and,Finset.prod_mul_distrib]
    ring
  · change |(A j).coeff*(B 0).coeff|≤1
    rw [abs_mul]
    exact (mul_le_mul (hAc j) (hBc 0) (abs_nonneg _) zero_le_one).trans_eq (one_mul _)

/-- A whole linear cell test has an exact product expansion with a
number of terms depending only on its coordinate budget. -/
theorem one_linear_design {R:ℕ} (t:Tagging p I)
    (L:OneKeys t N→ₗ[F]Vec (Fin R)) (φ:Wgt (Vec (Fin R))) (hφ:∀ x,|φ x|≤1):
    OneDesign t (φ ∘ L) (oneLinearPaletteSize I R) := by
  let E:=Fintype.equivFin (I→Vec (Fin R))
  let A (a:I→Vec (Fin R)):OnePaint t N:=
    ⟨φ (∑ i,a i),fun i x=>L (Pi.single i x)=a i⟩
  refine ⟨fun j=>A (E.symm j),funext fun x=>?_,fun j=>hφ _⟩
  have he:∑ i,L (Pi.single i (x i))=L x:=by rw [←map_sum,Finset.univ_sum_single]
  change φ (L x)=∑ j:Fin (oneLinearPaletteSize I R),_
  rw [←Equiv.sum_comp E]
  simp only [Equiv.symm_apply_apply,A]
  simp_rw [←ind_all,←funext_iff]
  rw [Finset.sum_eq_single (fun i=>L (Pi.single i (x i)))]
  · rw [ind_one rfl,mul_one,he]
  · intro a _ ha
    rw [ind_zero (Ne.symm ha),mul_zero]
  · simp

end
end Lax793645Proofs.Simplifications
