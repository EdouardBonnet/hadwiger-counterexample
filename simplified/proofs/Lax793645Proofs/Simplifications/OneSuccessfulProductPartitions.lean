import Lax793645Proofs.Simplifications.OneNaturalHistograms
import Lax793645Proofs.Simplifications.EquivariantProjection

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis Filter Finset Matrix Function
open scoped Classical BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
variable {p:Shape} {q:Format} {d:Rates} {side:Bool}

private theorem mapped_uniform_instances {A B:Type} (i j:Fintype A) (k:Fintype B)
    (E:A≃B) (P:B→Prop):
    @mapW A B i (@unifOn A j (P ∘ E)) E=@unifOn B k P := by
  cases Subsingleton.elim i j
  exact on_equiv E P

theorem one_design_mono {I:Type} [Fintype I] [DecidableEq I] {N:ℕ}
    (t:Tagging p I) (W:Wgt (OneKeys t N)) {k l:ℕ} (h:k≤l) (hW:OneDesign t W k):
    OneDesign t W l := by
  obtain ⟨A,hA,hAc⟩:=hW
  let B (j:Fin l):OnePaint t N:=if hj:j.val<k then A ⟨j.val,hj⟩ else ⟨0,fun _ _=>False⟩
  let inc:=Fin.castLE h
  have hi j:B (inc j)=A j:=by simp [B,inc]
  refine ⟨B,funext fun x=>?_,fun j=>?_⟩
  · rw [hA]
    unfold oneMural
    have he:(∑ j:Fin k,(A j).coeff*∏ i,ind ((A j).flies i (x i)))=
        ∑ j∈univ.image inc,(B j).coeff*∏ i,ind ((B j).flies i (x i)):=by
      rw [sum_image (Fin.castLE_injective h).injOn]
      exact sum_congr rfl (fun j _=>by rw [hi])
    rw [he]
    apply sum_subset (subset_univ _)
    intro j _ hj
    have hp:¬j.val<k:=fun he=>hj (mem_image.mpr ⟨⟨j.val,he⟩,mem_univ _,rfl⟩)
    simp only [B,dif_neg hp,zero_mul]
  · dsimp only [B]
    split_ifs
    · exact hAc _
    norm_num

/-- Each leaf has one bounded partition working for every orientation
filter; every union of its cells is an exact finite product test. -/
theorem one_successful_product_partition (w:Quill p q d side)
    (t:Tagging p (Messenger q)) [DecidableEq (KeySlots p t)]
    (z:Messenger q→F) (hw:w.moral t z) (hp:1≤p.r)
    (M:ℕ) (hM:1≤M) (c:ℝ):
    ∃ B:ℝ,1≤B ∧ ∀ ε:ℝ,0<ε → ∃ r paints:ℕ,∀ᶠ n:ℕ in atTop,
      ∀ (m:Mixer p n),Fintype.card (Row p n)+2*p.h+3≤M*n →
      ∀ (π:Wgt (OneUnit p n (M*n))),IsLaw π →
      (∀ o,π o≤bp (c*(M*n:ℕ))*oneUnitRaw m (M*n) o) →
      ∀ s:Charts p n d,∃ P:OneKeys t (M*n)→Fin r,
        (∀ H:Fin r→Prop,OneDesign t (fun x=>ind (H (P x))) paints) ∧
        ∀ F:OneUnit p n (M*n)→Prop,
        let ν:=oneLawNu p (M*n) t z;
        let D:=density ν (OneQuill.oneNaturalSales w t z π F m s);
        (∀ x,0≤banner ν P D x ∧ banner ν P D x≤B) ∧ lcost ν D (banner ν P D)≤ε := by
  obtain ⟨B,hB,hcal⟩:=one_successful_query_linear_partition w t z hw hp M hM c
  refine ⟨B,hB,fun ε hε=>?_⟩
  obtain ⟨R,hR⟩:=hcal ε hε
  refine ⟨Fintype.card (Vec (Fin R)),Fintype.card (Messenger q→Vec (Fin R)),?_⟩
  filter_upwards [hR] with n hn m hN π hπ hcap s
  obtain ⟨a,ha,C,hC⟩:=hn m hN π hπ hcap s
  have hcard:Fintype.card (Vec (Fin a))≤Fintype.card (Vec (Fin R)):=by
    simp only [Vec,Fintype.card_fun,Fintype.card_fin]
    exact Nat.pow_le_pow_right (by decide) ha
  let E:=oneQueryCoordinateEquiv t (M*n)
  let enc:Vec (Fin a)→Fin (Fintype.card (Vec (Fin R))):=
    (Fin.castLE hcard) ∘ Fintype.equivFin _
  have henc:Injective enc:=(Fin.castLE_injective hcard).comp (Fintype.equivFin _).injective
  let P:OneKeys t (M*n)→Fin (Fintype.card (Vec (Fin R))):=enc ∘ C.mulVec ∘ E.symm
  have hsize:Fintype.card (Messenger q→Vec (Fin a))≤Fintype.card (Messenger q→Vec (Fin R)):=by
    simpa only [Fintype.card_fun] using Nat.pow_le_pow_left hcard (Fintype.card (Messenger q))
  refine ⟨P,fun H=>?_,?_⟩
  · let L:OneKeys t (M*n)→ₗ[F]Vec (Fin a):=(Matrix.mulVecLin C).comp (oneKeyCoordinatesMap t (M*n))
    exact one_design_mono t _ hsize (one_linear_design t L (fun x=>ind (H (enc x)))
      (fun x=>(abs_of_nonneg (ind_nonneg _)).trans_le (ind_le_one _)))
  intro F ν D
  let ν':Wgt (KeyCoordinates (KeySlots p t) (M*n)):=unifOn (oneOwnPart t z)
  let D':=density ν' (oneSales w t z π F m s)
  have hν:mapW ν E.symm=ν':=by
    unfold ν ν' oneLawNu oneOwnKeyPart
    exact mapped_uniform_instances _ _ _ E.symm (oneOwnPart t z)
  have hsales:mapW (OneQuill.oneNaturalSales w t z π F m s) E.symm=oneSales w t z π F m s:=by
    funext k
    simp only [OneQuill.oneNaturalSales,mapW_equiv_val,Equiv.symm_symm,Equiv.symm_apply_apply,E]
  have hD:D'=D ∘ E:=by
    dsimp only [D']
    rw [←hsales,←hν,density_equivalence]
    rfl
  have hproj:(banner ν' C.mulVec D') ∘ E.symm=banner ν P D:=by
    have he:=banner_equivalence_input E.symm ν D C.mulVec
    rw [hν,Equiv.symm_symm,←hD] at he
    rw [show P=enc ∘ (C.mulVec ∘ E.symm) from rfl,banner_injective_output ν D _ enc henc]
    exact he
  have hc:=hC F
  constructor
  · intro x
    rw [←hproj]
    exact hc.1 (E.symm x)
  · have he:lcost ν D (banner ν P D)=lcost ν' D' (banner ν' C.mulVec D'):=by
      change avg ν (fun x=>|D x-banner ν P D x|)=avg ν' (fun x=>|D' x-banner ν' C.mulVec D' x|)
      rw [←hν,mapW_avg,hν]
      apply avg_congr
      intro x _
      have hd:D' (E.symm x)=D x:=by rw [hD]; simp
      rw [hd,←hproj]
      rfl
    rw [he]
    exact hc.2

end
end Lax793645Proofs.Simplifications
