import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.PredictedDualEvaluation
import Lax793645Proofs.Simplifications.PredictedOverlap

/-! Scalar generators with free role and basis coordinates. After subtracting
their prescribed linear terms, only the triple (q,f_A,f_B) remains constrained. -/
namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis Matrix Submodule LinearMap
open scoped BigOperators
noncomputable section
variable {d e : ℕ}

abbrev PredictedTriple := F × F × F

def predictedGenerator (α β : F) (X : Cell d) (Y : Cell e)
    (r : PredictedTriple) (u : Par d) (v : Par e) : Signal d e :=
  (r.1,(u,dotProduct X u.2+α*u.1+r.2.1),(v,dotProduct Y v.2+β*v.1+r.2.2))

def predictedSpan (α β : F) (X : Cell d) (Y : Cell e) (R : Set PredictedTriple) :
    Space (Signal d e) :=
  Submodule.span F {s | ∃ r ∈ R, ∃ u v, s=predictedGenerator α β X Y r u v}

theorem predicted_generator_mem (α β : F) (X : Cell d) (Y : Cell e)
    (R : Set PredictedTriple) {r : PredictedTriple} (hr : r ∈ R) (u : Par d) (v : Par e) :
    predictedGenerator α β X Y r u v ∈ predictedSpan α β X Y R :=
  Submodule.subset_span ⟨r,hr,u,v,rfl⟩

theorem predicted_covers (α β : F) (X : Cell d) (Y : Cell e) (R : Set PredictedTriple)
    (hR : ∀ q : F, ∃ f g, (q,f,g) ∈ R) : coverBase (predictedSpan α β X Y R) := by
  rintro ⟨q,u,v⟩
  obtain ⟨f,g,hfg⟩ := hR q
  exact ⟨⟨predictedGenerator α β X Y (q,f,g) u v,
    predicted_generator_mem α β X Y R hfg u v⟩,rfl⟩

set_option maxHeartbeats 800000 in
theorem predicted_dual_coefficients {A B : Rates} (α : Party)
    (X : ∀ i, Cell (A i)) (Y : ∀ i, Cell (B i))
    (R : Grid → Set PredictedTriple) (hR : ∀ i, (R i).Nonempty)
    (z : DualCoefficients A B)
    (hz : z.law (fun i => predictedSpan (α i.1) (α i.2) (X i.1) (Y i.2) (R i))) :
    (∀ i, z.north i = z.left i.2 • X i.1 ∧ z.south i = z.right i.1 • Y i.2) ∧
    (∀ i, z.hed i = z.left i.2 * PredictionClass.firstBit α i.1 ∧
      z.hed i = z.right i.1 * PredictionClass.firstBit α i.2) ∧
    ∀ i r, r ∈ R i → z.left i.2*r.2.1+z.right i.1*r.2.2=z.gam i*r.1 := by
  have hgen (i : Grid) (r : PredictedTriple) (hr : r ∈ R i) (u : Par (A i.1)) (v : Par (B i.2)) :
      z.gam i*r.1+z.hed i*(u.1+v.1)+(dotProduct (z.north i) u.2+dotProduct (z.south i) v.2) =
      z.left i.2*(u.1+(dotProduct (X i.1) u.2+α i.1*u.1+r.2.1)) +
      z.right i.1*(v.1+(dotProduct (Y i.2) v.2+α i.2*v.1+r.2.2)) :=
    hz i _ (predicted_generator_mem _ _ _ _ _ hr u v)
  have hzero i r (hr : r ∈ R i) : z.gam i*r.1=z.left i.2*r.2.1+z.right i.1*r.2.2 := by
    simpa using hgen i r hr 0 0
  have hbase i : z.north i=z.left i.2 • X i.1 ∧ z.south i=z.right i.1 • Y i.2 := by
    obtain ⟨r,hr⟩ := hR i
    constructor
    · ext k
      have hh := hgen i r hr (0,Pi.single k 1) 0
      simp only [Prod.fst_zero,Prod.snd_zero,zero_add,add_zero,mul_zero,dotProduct_zero,
        dotProduct_single,mul_one] at hh
      change z.north i k=z.left i.2*X i.1 k
      linear_combination hh-hzero i r hr
    · ext k
      have hh := hgen i r hr 0 (0,Pi.single k 1)
      simp only [Prod.fst_zero,Prod.snd_zero,zero_add,add_zero,mul_zero,dotProduct_zero,
        dotProduct_single,mul_one] at hh
      change z.south i k=z.right i.1*Y i.2 k
      linear_combination hh-hzero i r hr
  have hhead i : z.hed i=z.left i.2*PredictionClass.firstBit α i.1 ∧
      z.hed i=z.right i.1*PredictionClass.firstBit α i.2 := by
    obtain ⟨r,hr⟩ := hR i
    constructor
    · have hh := hgen i r hr (1,0) 0
      simp only [Prod.fst_zero,Prod.snd_zero,zero_add,add_zero,mul_zero,dotProduct_zero,mul_one] at hh
      unfold PredictionClass.firstBit
      linear_combination hh-hzero i r hr
    · have hh := hgen i r hr 0 (1,0)
      simp only [Prod.fst_zero,Prod.snd_zero,zero_add,add_zero,mul_zero,dotProduct_zero,mul_one] at hh
      unfold PredictionClass.firstBit
      linear_combination hh-hzero i r hr
  exact ⟨hbase,hhead,fun i r hr => (hzero i r hr).symm⟩

end
end Lax793645Proofs.Simplifications
