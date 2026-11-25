import Lax793645Proofs.Simplifications.PredictedGenerators

/-! Finite predictor cells determine soluble scalar systems directly. A dual
relation is exact on every retained cell, so its reference error is at most
the total weight of the discarded cells. -/
namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis StatusAnalysis.DualAnalysis PredictionClass
open Finset Matrix Function
open scoped BigOperators
noncomputable section
variable {p : Shape} {n N r : ℕ} {A B : Rates}

def retainedPatterns (u : Terrain p r) (f : Bool → Pulsar p r) (η : ℝ)
    (i : Grid) : Set PredictedTriple :=
  {v | ∃ (l : Tag p.g) (k : Fin r), η ≤ u l v.1 k ∧
    v.2.1=f i.1 l v.1 k ∧ v.2.2=f i.2 l v.1 k}

theorem retained_cell_exists (u : Wgt (Fin r)) (hu : IsLaw u) {η : ℝ}
    (hη : (r:ℝ)*η < 1) : ∃ k, η ≤ u k := by
  by_contra! h
  have hh := Finset.sum_le_sum (s:=univ) (fun k _ => (h k).le)
  have ht : (∑ k : Fin r, u k)=1 := hu.total
  simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] at hh
  linarith

theorem retained_covers (u : Terrain p r) (f : Bool → Pulsar p r) (η : ℝ)
    (hu : ∀ l q, IsLaw (u l q)) (hη : (r:ℝ)*η < 1) (hg : 0 < p.g)
    (i : Grid) (q : F) : ∃ a b, (q,a,b) ∈ retainedPatterns u f η i := by
  let l : Tag p.g := ⟨0,hg⟩
  obtain ⟨k,hk⟩ := retained_cell_exists (u l q) (hu l q) hη
  exact ⟨f i.1 l q k,f i.2 l q k,l,k,hk,rfl,rfl⟩

theorem retained_relation_cost (v : PredictionData p A B r) (u : Terrain p r)
    (z : DualCoefficients A B) (η : ℝ) (hη : 0 ≤ η)
    (hu : ∀ l q, IsLaw (u l q))
    (h : ∀ i x, x ∈ retainedPatterns u v.g η i →
      z.left i.2*x.2.1+z.right i.1*x.2.2=z.gam i*x.1) :
    ∀ i l q, ChorusCost v z i u l q ≤ (r:ℝ)*η := by
  intro i l q
  apply (pr_mono (hu l q).nz (q:=fun k => u l q k < η) ?_).trans
    (haze_small (u l q) η hη)
  intro k hk
  apply lt_of_not_ge
  intro hlarge
  exact hk (h i (q,v.g i.1 l q k,v.g i.2 l q k) ⟨l,k,hlarge,rfl,rfl⟩)

theorem retained_scalar_soluble (v : PredictionData p A B r) (u : Terrain p r)
    (c : PredictionClass) (τ η : ℝ) (m : BMark p n N)
    (x y : UnitType p n N) (T : Cross p n) (s : Charts p n A) (t : Charts p n B)
    (hx : coordSpec m x s v.X) (hy : coordSpec m y t v.Y) (hg : 3 ≤ p.g)
    (hclass : chorusClass p v u c τ) (hu : ∀ l q, IsLaw (u l q))
    (he : glint p (m x)=glint p (m y))
    (hcompat : c.compatible v.α (glint p (m x))
      (cardTone m x T,cardTone m y (reciprocal p T)))
    (hη : 0 ≤ η) (hτ : (r:ℝ)*η ≤ τ) (hsmall : 2*τ < 1) :
    scorecard (fun i => predictedSpan (v.α i.1) (v.α i.2) (v.X i.1) (v.Y i.2)
      (retainedPatterns u v.g η i)) (hailing p s t T) := by
  have hτ0 : 0 ≤ τ := (mul_nonneg (Nat.cast_nonneg r) hη).trans hτ
  have hrη : (r:ℝ)*η < 1 := by linarith
  have hcover i := predicted_covers (v.α i.1) (v.α i.2) (v.X i.1) (v.Y i.2)
    (retainedPatterns u v.g η i) (retained_covers u v.g η hu hrη (by omega) i)
  by_contra h
  obtain ⟨z,hz,hlaw,hbad⟩ := jargon_score _ _ h hcover
  have hnonempty i : (retainedPatterns u v.g η i).Nonempty := by
    obtain ⟨a,b,hab⟩ := retained_covers u v.g η hu hrη (by omega) i 0
    exact ⟨(0,a,b),hab⟩
  obtain ⟨hbase,hhead,hrelations⟩ := predicted_dual_coefficients v.α v.X v.Y _ hnonempty z hlaw
  apply hbad
  exact harmony v u c τ m x y T s t hx hy hg hclass hu he hcompat z hτ0 hsmall hz hbase hhead
    (fun i l q => (retained_relation_cost v u z η hη hu hrelations i l q).trans hτ)

end
end Lax793645Proofs.Simplifications
