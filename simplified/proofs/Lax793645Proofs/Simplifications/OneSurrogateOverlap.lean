import Lax793645Proofs.Simplifications.OneProjectedComparison

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis Finset Function
open scoped Classical BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

private theorem uniform_average_instances {A : Type} (i j k l : Fintype A)
    (P : A→Prop) (f : Wgt A) :
    @avg A i (@unifOn A j P) f=@avg A k (@unifOn A l P) f := by
  cases Subsingleton.elim i k
  cases Subsingleton.elim j l
  rfl

theorem dip_mixture_product {A I J : Type} [Fintype A] [Fintype I] [Fintype J]
    (ν : Wgt A) (μ : Wgt I) (ρ : Wgt J) (f : I→Wgt A) (g : J→Wgt A) :
    dip ν (mixW μ f) (mixW ρ g)=avg (pairW μ ρ) (fun ij=>dip ν (f ij.1) (g ij.2)) := by
  unfold dip mixW
  have he x : avg μ (fun i=>f i x)*avg ρ (fun j=>g j x)=
      avg (pairW μ ρ) (fun ij=>f ij.1 x*g ij.2 x):=(pairW_separate ..).symm
  simp_rw [he]
  exact avg_avg ..

variable {p : Shape} {n N r : ℕ} {q : Format} {d e : Rates}

theorem one_reference_integral (t : Tagging p (Messenger q)) (z : Messenger q→F)
    (f : Wgt (KeyCoordinates (KeySlots p t) N)) :
    avg (unifOn (oneOwnPart t z)) f=
      avg (oneLawNu p N t z) (f∘(oneQueryCoordinateEquiv t N).symm) := by
  have h:=mapW_avg (oneLawNu p N t z) (oneQueryCoordinateEquiv t N).symm f
  rw [one_reference_coordinates] at h
  convert h using 1
  all_goals
    try unfold oneLawNu
    exact uniform_average_instances _ _ _ _ _ _

theorem one_reference_dip (t : Tagging p (Messenger q)) (z : Messenger q→F)
    (f g : Wgt (OneKeys t N)) :
    dip (unifOn (oneOwnPart t z)) (f∘oneQueryCoordinateEquiv t N) (g∘oneQueryCoordinateEquiv t N)=
      dip (oneLawNu p N t z) f g := by
  unfold dip
  rw [one_reference_integral]
  apply avg_congr
  intro x _
  simp only [Function.comp_apply,Equiv.apply_symm_apply]

namespace OneTypus
variable (w : Typus p q d e) (μ ρ : Wgt (OneUnit p n N))
  (F G : OneUnit p n N→Prop) (s : Charts p n d) (t : Charts p n e)
  (m : Mixer p n) (Y : OneSilhouette p N r)

def oneFilteredScore:=avg (pairW μ ρ) (fun o=>ind (F o.1 ∧ G o.2)*oneConstellation w o.1 o.2 s t m Y)

theorem one_constellation_nonneg (o o' : OneUnit p n N)
    (ha : ∀ i,IsLaw (w.qA.policies w.t w.z n i))
    (hb : ∀ i,IsLaw (w.qB.policies w.t w.z n i)) :
    0≤oneConstellation w o o' s t m Y := by
  apply mul_nonneg (mul_nonneg (one_kappa_pos _).le (one_kappa_pos _).le)
  apply prod_nonneg
  intro i _
  exact avg_nonneg (fun x=>map_nz (unifOn_sub _).nz _ x) (fun x=>mul_nonneg
    (OneQuill.one_seraph_floor w.qA w.t w.z o m s Y i (ha i) x).1
    (OneQuill.one_seraph_floor w.qB w.t w.z o' m t Y i (hb i) x).1)

theorem one_showcase_pair :
    dip (oneLawNu p N w.t w.z) (OneQuill.oneShowcase w.qA w.t w.z μ F m s Y)
      (OneQuill.oneShowcase w.qB w.t w.z ρ G m t Y)=
      avg (pairW μ ρ) (fun o=>ind (F o.1 ∧ G o.2)*
        dip (oneLawNu p N w.t w.z) (OneQuill.oneMirror w.qA w.t w.z o.1 m s Y)
          (OneQuill.oneMirror w.qB w.t w.z o.2 m t Y)) := by
  change dip _ (mixW μ _) (mixW ρ _)=_
  rw [dip_mixture_product]
  apply avg_congr
  intro o _
  unfold dip
  rw [←avg_mul']
  exact avg_congr (fun x _=>by rw [ind_and]; ring)

theorem one_filtered_shine (hμ : IsLaw μ) (hρ : IsLaw ρ)
    (ha : ∀ i,IsLaw (w.qA.policies w.t w.z n i))
    (hb : ∀ i,IsLaw (w.qB.policies w.t w.z n i))
    (hN : 2*num (Messenger q×Toast p)+2≤(N:ℝ)) :
    |oneFilteredScore w μ ρ F G s t m Y-
      dip (oneLawNu p N w.t w.z) (OneQuill.oneShowcase w.qA w.t w.z μ F m s Y)
        (OneQuill.oneShowcase w.qB w.t w.z ρ G m t Y)|≤
      2*quadraticNetFact (trayPort p w.t)*bp (-(N:ℝ)/2) := by
  rw [oneFilteredScore,one_showcase_pair,←avg_sub]
  apply (abs_avg_le (pairW_law hμ hρ).nz).trans
  apply (pairW_law hμ hρ).avg_le
  intro o
  rw [←mul_sub,abs_mul,abs_of_nonneg (ind_nonneg _)]
  exact ((mul_le_mul_of_nonneg_right (ind_le_one _) (abs_nonneg _)).trans_eq (one_mul _)).trans
    (one_shine_match w o.1 o.2 s t m Y ha hb hN)

/-- Finite-table overlap is controlled by the common projection of the
actual query measures and their projected distribution errors. -/
theorem one_projected_surrogate_mend {A : Type} [Fintype A]
    (P : KeyCoordinates (KeySlots p w.t) N→A)
    (hμ : IsLaw μ) (hρ : IsLaw ρ)
    (ha : ∀ i,IsLaw (w.qA.policies w.t w.z n i))
    (hb : ∀ i,IsLaw (w.qB.policies w.t w.z n i))
    (hν : IsLaw (unifOn (oneOwnPart (N:=N) w.t w.z))) :
    let ν:=unifOn (oneOwnPart (N:=N) w.t w.z)
    let QA:=oneSales w.qA w.t w.z μ F m s
    let QB:=oneSales w.qB w.t w.z ρ G m t
    dip (oneLawNu p N w.t w.z) (OneQuill.oneShowcase w.qA w.t w.z μ F m s Y)
      (OneQuill.oneShowcase w.qB w.t w.z ρ G m t Y)^2≤
      dip ν (banner ν P (density ν QA)) (banner ν P (density ν QB))+
        (varOne (mapW (OneQuill.oneDisplayCoordinates w.qA w.t w.z μ F m s Y) P) (mapW QA P)+
        varOne (mapW (OneQuill.oneDisplayCoordinates w.qB w.t w.z ρ G m t Y) P) (mapW QB P)) := by
  intro ν QA QB
  let f:=OneQuill.oneShowcase w.qA w.t w.z μ F m s Y
  let g:=OneQuill.oneShowcase w.qB w.t w.z ρ G m t Y
  let E:=oneQueryCoordinateEquiv w.t N
  have hf:=OneQuill.one_showcase_bound w.qA w.t w.z μ F m s Y hμ ha
  have hg:=OneQuill.one_showcase_bound w.qB w.t w.z ρ G m t Y hρ hb
  have hh:=projected_density_mend ν hν P (f∘E) (g∘E) QA QB
    ⟨fun x=>hf.1 _,fun x=>hf.2 _⟩ ⟨fun x=>hg.1 _,fun x=>hg.2 _⟩
    (one_sales_nonneg w.qA w.t w.z μ F m s hμ.nz)
    (one_sales_nonneg w.qB w.t w.z ρ G m t hρ.nz)
    (OneQuill.one_sales_support w.qA w.t w.z μ F m s)
    (OneQuill.one_sales_support w.qB w.t w.z ρ G m t)
  have hA : (fun x=>ν x*(f∘E) x)=OneQuill.oneDisplayCoordinates w.qA w.t w.z μ F m s Y :=
    funext (fun x=>(OneQuill.one_display_coordinates_value w.qA w.t w.z μ F m s Y x).symm)
  have hB : (fun x=>ν x*(g∘E) x)=OneQuill.oneDisplayCoordinates w.qB w.t w.z ρ G m t Y :=
    funext (fun x=>(OneQuill.one_display_coordinates_value w.qB w.t w.z ρ G m t Y x).symm)
  rw [hA,hB] at hh
  change dip (unifOn (oneOwnPart w.t w.z)) (f∘oneQueryCoordinateEquiv w.t N)
    (g∘oneQueryCoordinateEquiv w.t N)^2≤_ at hh
  rw [one_reference_dip] at hh
  exact hh

end OneTypus
end
end Lax793645Proofs.Simplifications
