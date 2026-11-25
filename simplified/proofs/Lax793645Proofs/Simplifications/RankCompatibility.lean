import Lax793645Proofs.Simplifications.PredictedOverlap
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.CoverAlternatives

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix Function PredictionClass
noncomputable section

theorem iid_pair_probability {A I : Type} [Fintype A] [Fintype I] [DecidableEq I]
    (μ : Wgt A) (hμ : IsLaw μ) (i j : I) (hij : i ≠ j) (P : A × A → Prop) :
    pr (prodW (fun _ : I => μ)) (fun x => P (x i,x j)) = pr (pairW μ μ) P := by
  classical
  let e : Unit ⊕ Unit → I := Sum.elim (fun _ => i) (fun _ => j)
  have he : Injective e := by
    intro a b h
    cases a <;> cases b <;> simp_all [e]
  let f (x : I → A) (_ : Unit) := (x i,x j)
  have hf := prodW_map_pairs e he hμ
  change mapW (prodW (fun _ : I => μ)) f = prodW (fun _ : Unit => pairW μ μ) at hf
  have hh := mapW_pr (prodW (fun _ : I => μ)) f (fun x => ∀ k : Unit, P (x k))
  rw [hf,prodW_pr] at hh
  simpa only [f,forall_const,Fintype.prod_unique] using hh.symm

theorem alternating_zero_probability {A : Type} [Fintype A]
    (μ : Wgt A) (hμ : IsLaw μ) (H : Mat A A) (r : ℕ)
    (hr : H.rank ≤ r) (hdiag : ∀ a, H a a=0) :
    1/(r+2:ℝ)^2 ≤ pr (pairW μ μ) (fun x => H x.1 x.2=0) := by
  let P := fun x : A×A => H x.1 x.2=0
  have h := zero_pair_probability (prodW (fun _ : Fin (r+2) => μ))
    (prodW_law fun _ => hμ) H r hr hdiag (fun x => x) (pr (pairW μ μ) P)
    (pr_nonneg (pairW_law hμ hμ).nz)
    (fun i j hij => (iid_pair_probability μ hμ i j hij P).le)
  exact (div_le_iff₀ (by positivity)).mpr (by simpa only [mul_comm] using h)

theorem twinned_rank_compatibility {p : Shape} {n N : ℕ}
    (T : Cov p N) (d : ℕ) (hd : cdim p T ≤ d) (α : Party) (r : F)
    (Δ : UnitType p n N → Ambient p N) (μ : Wgt (UnitType p n N))
    (hμ : IsLaw μ) (hcover : ∀ x, μ x ≠ 0 → covered p T (Δ x)) :
    1/(2*d*N+2:ℝ)^2 ≤ pr (pairW μ μ) (matchUp Δ α r PredictionClass.twinned) := by
  obtain ⟨H,hH,hdiag,hmatch⟩ := matSeason T d hd α r Δ μ hcover
  have h := alternating_zero_probability μ hμ H (2*d*N) hH hdiag
  have he : pr (pairW μ μ) (fun x => H x.1 x.2=0) =
      pr (pairW μ μ) (matchUp Δ α r PredictionClass.twinned) :=
    avg_congr fun x hx => congrArg ind (propext (hmatch x hx))
  rw [he] at h
  exact_mod_cast h

end
end Lax793645Proofs.Simplifications
