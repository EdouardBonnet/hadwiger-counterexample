import Lax793645Proofs.Simplifications.LinearPartitionPaints
import Lax793645Proofs.Simplifications.PredictorCells

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis Template Finset Matrix Function
open scoped Classical
noncomputable section
variable {p : Shape} {I : Type} [Fintype I] [DecidableEq I] {N : ℕ}

theorem unary_product_design (v : Template p I)
    (P : ∀ i,AtomKey (p:=p) (v.t i) N→Prop) :
    design v (fun x=>ind (∀ i,P i (x i))) 1 1 := by
  refine ⟨fun _=>⟨1,P⟩,funext fun x=>?_,fun _=>by norm_num⟩
  simp only [mural,Paint.cost,Fin.sum_univ_one,one_mul,prodW,ind_all]

theorem all_keys_design (v : Template p I) :
    design v (fun _ : Keys (p:=p) v.t N=>ind True) 1 1 := by
  simpa using unary_product_design v (fun _ _=>True)

theorem tuple_cell_design {q : Format} (v : Template p (Messenger q))
    {r : ℕ} (Y : Silhouette p N r) (z : Messenger q→F) (a : Messenger q→Fin r) :
    design v (fun x=>ind (tupleCell Y v.t z a x)) 1 1 :=
  unary_product_design v (fun i x=>Y (v.t i) (z i) x=a i)

theorem design_mul_one (v : Template p I) (f g : Wgt (Keys (p:=p) v.t N))
    (r : ℕ) (hf : design v f 1 r) (hg : design v g 1 1) :
    design v (fun x=>f x*g x) 1 r := by
  obtain ⟨F,hF,hFc⟩:=hf
  obtain ⟨G,hG,hGc⟩:=hg
  let H (i : Fin r) : Paint v N:=
    ⟨(F i).coeff*(G 0).coeff,fun j x=>(F i).flies j x ∧ (G 0).flies j x⟩
  refine ⟨H,funext fun x=>?_,fun i=>?_⟩
  · rw [hF,hG]
    simp only [mural,Fin.sum_univ_one]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    simp only [H,Paint.cost,prodW,ind_and,Finset.prod_mul_distrib]
    ring
  · change |(F i).coeff*(G 0).coeff|≤1
    rw [abs_mul]
    exact (mul_le_mul (hFc i) (hGc 0) (abs_nonneg _) zero_le_one).trans_eq (one_mul _)

theorem quill_design_transfer {q : Format} {d e : Rates} {b b' : Bool}
    (wA : Quill p q d b) (wB : Quill p q e b') (t : Tagging p (Messenger q))
    (f : Wgt (Keys (p:=p) t N)) (r : ℕ) (hf : design (wA.pen t) f 1 r) :
    design (wB.pen t) f 1 r := by
  obtain ⟨F,hF,hFc⟩:=hf
  refine ⟨fun i=>⟨(F i).coeff,(F i).flies⟩,?_,hFc⟩
  rw [hF]
  rfl

end
end Lax793645Proofs.Simplifications
