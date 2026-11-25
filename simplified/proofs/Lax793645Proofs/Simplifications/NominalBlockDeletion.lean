import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.MatrixRankCounting

/-! # Deleting dependent nominal query blocks

The deletion statement handles dependencies spread across many blocks.
Its probability corollary is for uniform binary matrices; transfer to the
actual nominal query law and the Fourier expansion of deleted factors are
separate parts of the capped-leaf estimate.
-/

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function Submodule
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {T I U : Type} [Fintype T] [Fintype I] [Fintype U]
  [DecidableEq T] [DecidableEq I] [DecidableEq U]

omit [Fintype U] [DecidableEq U] in
/-- A nominal column family of rank deficiency d can be made independent
by deleting at most d whole query blocks. Dependencies need not be local. -/
theorem independent_after_block_deletion (P : Mat U (T×I)) :
    ∃ S : Finset T,S.card≤Fintype.card (T×I)-P.rank ∧
      LinearIndependent F (fun v : {v : T×I // v.1∉S}=>P.col v.val) := by
  classical
  obtain ⟨κ,a,ha,hspan,hli⟩ := exists_linearIndependent' F P.col
  let : Finite κ := Finite.of_injective a ha
  let : Fintype κ := Fintype.ofFinite κ
  let B : Finset (T×I) := Finset.univ.image a
  let S : Finset T := (Finset.univ\B).image Prod.fst
  have hcard : B.card=P.rank := by
    rw [Finset.card_image_of_injective _ ha,Finset.card_univ]
    rw [Matrix.rank_eq_finrank_span_cols,←hspan,finrank_span_eq_card hli]
  refine ⟨S,?_,?_⟩
  · exact Finset.card_image_le.trans (by
      rw [Finset.card_sdiff,Finset.inter_univ,Finset.card_univ,hcard])
  · have hex (v : {v : T×I // v.1∉S}) : ∃ k : κ,a k=v.val := by
      have hv : v.val∈B := by
        by_contra hn
        exact v.property (Finset.mem_image.mpr
          ⟨v.val,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hn⟩,rfl⟩)
      obtain ⟨k,_,hk⟩ := Finset.mem_image.mp hv
      exact ⟨k,hk⟩
    choose e he using hex
    have hei : Injective e := by
      intro v w h
      apply Subtype.ext
      rw [←he v,←he w,h]
    have hh := hli.comp e hei
    simpa only [Function.comp_def,he] using hh

/-- A raw independent matrix has exponentially small probability of needing
more than d block deletions. The quantitative cost is kept before any cap. -/
theorem block_deletion_tail (d : ℕ) :
    pr unif (fun P : Mat U (T×I)=>
      ¬∃ S : Finset T,S.card≤d ∧
        LinearIndependent F (fun v : {v : T×I // v.1∉S}=>P.col v.val))≤
      bp ((num (T×I)-num U)*(d+1)) := by
  classical
  refine (pr_mono unif_law.nz (fun P hP=>?_)).trans
    (by simpa only [Nat.cast_add,Nat.cast_one] using
      pr_deficient (I:=U) (J:=T×I) (d+1))
  obtain ⟨S,hS,hi⟩ := independent_after_block_deletion P
  have hn : d<S.card := lt_of_not_ge (fun h=>hP ⟨S,h,hi⟩)
  omega

end
end Lax793645Proofs.Simplifications
