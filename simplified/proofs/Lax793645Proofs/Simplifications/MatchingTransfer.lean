import Lax793645Proofs.Simplifications.ExposureTree
import Lax793645Proofs.Simplifications.MatchingSampling

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Lax793645Proofs.Upstream.OAI.HadwigerMatching
open scoped BigOperators
noncomputable section
variable {A : Type*} [Fintype A] [Nonempty A]

/-- Graph transfer by finite clipped-probability exposure, without containers,
convex minimizers or a terminal cut. Both endpoint marginals are trimmed, so
the matching edges can retain their fixed orientations. -/
theorem matching_exposure_transfer (H : Holes A) {μ : Wgt A} (hμ : IsLaw μ)
    {M D ε : ℝ} (hM : 0 < M) (hD : 0 < D) (hε : 0 < ε)
    (hsat : ∀ w, IsLaw w → pairCaps μ M D w → carried w H.unit →
      ε ≤ pr (pairW w w) (fun z => H.conflict z.1 z.2))
    {L b m k s : ℕ} (hb : 0 < b) (hk : 0 < k) (hkm : 100*k < m+100) (hs : 4*s ≤ k)
    (hscale : D ≤ (2:ℝ)^b*(ε/32)) (hbudget : 384*(b:ℝ) < (L:ℝ)*ε)
    (herr : ((Fintype.card (A × A):ℝ)+1)^L *
      ((2:ℝ)^m*(8/M)^s+(m:ℝ)^(s+s)*(4/D)^s) < 1/8) :
    ∃ x : Fin m → A, (H.graph x).indepNum ≤ 2 ∧
      (connectedMatchingNumber (H.graph x):ℚ) < (m:ℚ)/100 := by
  classical
  by_contra hn
  have hmatch (x : Fin m → A) :
      ∃ e : Fin k ⊕ Fin k → Fin m, Function.Injective e ∧
        (∀ i, H.unit (x (e (.inl i)),x (e (.inr i)))) ∧
        (∀ i j, ¬H.conflict (x (e (.inl i)),x (e (.inr i)))
          (x (e (.inl j)),x (e (.inr j)))) := by
    have ht : k ≤ connectedMatchingNumber (H.graph x) := by
      have hnot : ¬ (connectedMatchingNumber (H.graph x):ℚ)<(m:ℚ)/100 :=
        fun h => hn ⟨x,H.indepNum_graph_le x,h⟩
      have hr : (m:ℚ) ≤ 100*(connectedMatchingNumber (H.graph x):ℚ) := by linarith
      have hr' : m ≤ 100*connectedMatchingNumber (H.graph x) := by exact_mod_cast hr
      omega
    obtain ⟨e,he,hu,hc⟩ := H.matching_pairs x
    let f : Fin k → Fin (connectedMatchingNumber (H.graph x)) := Fin.castLE ht
    have hf : Function.Injective f := Fin.castLE_injective ht
    exact ⟨e ∘ Sum.map f f, he.comp (Sum.map_injective.mpr ⟨hf,hf⟩),
      fun i => hu (f i),fun i j => hc (f i) (f j)⟩
  choose e he hu hc using hmatch
  letI : NeZero k := ⟨Nat.ne_of_gt hk⟩
  let f (x : Fin m → A) (i : Fin k) := (x (e x (.inl i)),x (e x (.inr i)))
  let K (x : Fin m → A) := mapW (unif : Wgt (Fin k)) (f x)
  let π := prodW (fun _ : Fin m => μ)
  have hπ : IsLaw π := prodW_law fun _ => hμ
  have hK x : IsLaw (K x) := mapW_law unif_law (f x)
  let ρ := historyState π K
  let σ h := forecast (ρ h) K
  let S h := heavyEndpoints μ M (σ h)
  let E h := heavyPairs μ D (σ h)
  let T := shortHistories (X:=A × A) L
  let bad (x : Fin m → A) := ∃ h : T, badS (S h.val) s x ∨ badE (E h.val) s x
  have hσ h : IsLaw (σ h) := forecast_law (historyState_law hπ hK h) hK
  have hbad : pr π bad < 1/8 := by
    let err := (2:ℝ)^m*(8/M)^s+(m:ℝ)^(s+s)*(4/D)^s
    have hp (h : T) : pr π (fun x => badS (S h.val) s x ∨ badE (E h.val) s x) ≤ err := by
      have h₁ := badS_pr hμ (S h.val) s m
      have h₂ := badE_pr hμ (E h.val) s m
      have hs' : pr μ (S h.val) ≤ 8/M := heavyEndpoints_mass hμ hM (hσ h.val)
      have he' : pr (pairW μ μ) (E h.val) ≤ 4/D := heavyPairs_mass hD (hσ h.val)
      have hn₁ := pr_nonneg (p:=S h.val) hμ.nz
      have hn₂ := pr_nonneg (p:=E h.val) (pairW_law hμ hμ).nz
      refine (pr_or_le hπ.nz).trans ((add_le_add h₁ h₂).trans ?_)
      dsimp only [err]
      gcongr
    have ht : (T.card:ℝ) ≤ ((Fintype.card (A × A):ℝ)+1)^L := by
      exact_mod_cast card_shortHistories (X:=A × A) L
    have hp' : pr π bad ≤ (T.card:ℝ)*err := by
      refine (pr_exists_le hπ.nz (fun h : T => fun x => badS (S h.val) s x ∨ badE (E h.val) s x)).trans ?_
      have ha := Finset.sum_le_sum (fun h (_ : h ∈ Finset.univ) => hp h)
      simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul] using ha
    exact lt_of_le_of_lt (hp'.trans (mul_le_mul_of_nonneg_right ht (by dsimp [err]; positivity))) herr
  apply exposure_tree_impossible H hμ hM hD hε hsat π K hπ hK
    (fun x => map_carried _ (f x) H.unit (hu x))
    (fun x y z hz => map_nonconflict _ (f x) H.conflict (hc x) y z hz)
    bad hbad L b hb hscale hbudget
  intro h hh x hx
  have hm : h ∈ T := (mem_shortHistories h L).mpr hh
  apply matching_retained_mass hk hs x (e x) (he x) (S h) (E h)
  exact fun hb => hx ⟨⟨h,hm⟩,hb⟩

end
end Lax793645Proofs.Simplifications
