import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.FrameOrbitLaws
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.AmbientBatchSlots

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix Function
noncomputable section
set_option backward.isDefEq.respectTransparency false

def splitFirstRow (n N : ℕ) :
    Vec (Fin n)×Mat (Fin N) (Fin n)≃Mat (Option (Fin N)) (Fin n) where
  toFun z i j := i.elim (z.1 j) (fun i=>z.2 i j)
  invFun M := (M none,fun i j=>M (some i) j)
  left_inv z := by rfl
  right_inv M := by ext i j; cases i <;> rfl

theorem first_row_zero_injective (n N : ℕ) (M : Mat (Fin N) (Fin n)) :
    Injective (splitFirstRow n N (0,M)).mulVec ↔ Injective M.mulVec := by
  constructor
  · intro hi x y hxy
    apply hi
    funext i
    cases i with
    | none => simp [Matrix.mulVec,splitFirstRow,dotProduct]
    | some i => exact congr_fun hxy i
  · intro hi x y hxy
    apply hi
    exact funext (fun i=>congr_fun hxy (some i))

/-- A fixed ambient coordinate can vanish on every column of a uniform
injective frame with probability at least 2^(-n-1). Conditioning on this
event is therefore permitted by an exponential cap of 2^(n+1). -/
theorem injective_frame_zero_row_mass (n N : ℕ) (hN : n+1≤N) :
    bp (-((n:ℝ)+1))≤pr
      (unifOn (fun M : Mat (Option (Fin N)) (Fin n)=>Injective M.mulVec))
      (fun M=>M none=0) := by
  classical
  let E := splitFirstRow n N
  let U := Mat (Option (Fin N)) (Fin n)
  let good (M : U) := Injective M.mulVec
  let row (M : U) := M none=0
  have hz : pr unif (fun x : Vec (Fin n)=>x=0)=bp (-(n:ℝ)) := by
    have hh := pr_unif_lin (LinearMap.id : Vec (Fin n)→ₗ[F] Vec (Fin n)) 0
    rw [ind_one (LinearMap.range (LinearMap.id : Vec (Fin n)→ₗ[F] Vec (Fin n))).zero_mem,one_mul] at hh
    have hr := rk_inj.mp (show Injective
      (LinearMap.id : Vec (Fin n)→ₗ[F] Vec (Fin n)) from fun _ _ h=>h)
    rw [dim_vec,Fintype.card_fin] at hr
    rw [hr] at hh
    exact hh
  have htail : (1:ℝ)/2≤pr unif (fun M : Mat (Fin N) (Fin n)=>Injective M.mulVec) := by
    have hh := @unif_fail (Fin n) (Fin N) _ _ _ _
    have he : bp (num (Fin n)-num (Fin N))≤(1:ℝ)/2 := by
      have hnum : (n:ℝ)-(N:ℝ)≤-1 := by exact_mod_cast (show (n:ℤ)-(N:ℤ)≤-1 by omega)
      have hb := bp_le hnum
      simpa [num,bp_neg,bp_one] using hb
    have hp := pr_not (unif : Wgt (Mat (Fin N) (Fin n))) (fun M=>Injective M.mulVec)
    rw [unif_law.total] at hp
    linarith
  have hjoint : pr (unif : Wgt U) (fun M=>good M∧row M)=
      bp (-(n:ℝ))*pr unif (fun M : Mat (Fin N) (Fin n)=>Injective M.mulVec) := by
    have he := mapW_pr (unif : Wgt (Vec (Fin n)×Mat (Fin N) (Fin n))) E (fun M=>good M∧row M)
    rw [unif_equiv,pair_unif] at he
    rw [he]
    have hh (z : Vec (Fin n)×Mat (Fin N) (Fin n)) :
        good (E z)∧row (E z) ↔ z.1=0 ∧ Injective z.2.mulVec := by
      change Injective (splitFirstRow n N z).mulVec ∧ z.1=0 ↔ _
      rcases z with ⟨v,M⟩
      by_cases hv : v=0
      · subst v
        simp only [first_row_zero_injective,true_and,and_true]
      · simp [hv]
    simp_rw [hh]
    have hp := pairW_pr (unif : Wgt (Vec (Fin n)))
      (unif : Wgt (Mat (Fin N) (Fin n)))
      (fun v : Vec (Fin n)=>v=0) (fun M : Mat (Fin N) (Fin n)=>Injective M.mulVec)
    rw [hz] at hp
    exact hp
  have hpos : 0<pr (unif : Wgt U) good := by
    have hj : 0<pr (unif : Wgt U) (fun M=>good M∧row M) := by
      rw [hjoint]
      exact mul_pos (bp_pos _) (lt_of_lt_of_le (by norm_num) htail)
    exact hj.trans_le (pr_mono unif_law.nz (fun _ h=>h.1))
  have hle : pr (unif : Wgt U) good≤1 := by
    simpa only [unif_law.total] using pr_le_tot (p:=good) unif_law.nz
  change _≤pr (unifOn good) row
  rw [←on_unif,pr_on,hjoint]
  calc
    bp (-((n:ℝ)+1))=bp (-(n:ℝ))*((1:ℝ)/2) := by
      rw [neg_add,bp_add,bp_neg (1:ℝ),bp_one]
      ring
    _≤bp (-(n:ℝ))*pr unif (fun M : Mat (Fin N) (Fin n)=>Injective M.mulVec) :=
      mul_le_mul_of_nonneg_left htail (bp_pos _).le
    _≤_ := le_div_self (mul_nonneg (bp_pos _).le (pr_nonneg unif_law.nz)) hpos hle

/-- An exponentially capped law on injective frames under which a fixed,
nonzero ambient coordinate has identically zero pullback. This rules out
deducing full pullback rank from the density cap alone. -/
theorem capped_zero_pullback (n N : ℕ) (hN : n+1≤N) :
    let μ := unifOn (fun M : Mat (Option (Fin N)) (Fin n)=>Injective M.mulVec)
    ∃ π : Wgt (Mat (Option (Fin N)) (Fin n)),IsLaw π ∧
      (∀ M,π M≤bp ((n:ℝ)+1)*μ M) ∧
      pr π (fun M=>M none=0)=1 ∧
      carried π (fun M=>∀ z : Vec (Fin n),(M*ᵥz) none=0) := by
  classical
  intro μ
  let E (M : Mat (Option (Fin N)) (Fin n)) := M none=0
  let π := onW μ E
  have hmass : bp (-((n:ℝ)+1))≤pr μ E := injective_frame_zero_row_mass n N hN
  have hpos : 0<pr μ E := (bp_pos _).trans_le hmass
  have hμ : ∀ M,0≤μ M := (unifOn_sub _).nz
  have hπ : IsLaw π := normW_law (subW_nonneg hμ _) hpos
  refine ⟨π,hπ,?_,?_,?_⟩
  · intro M
    have hh := on_mon hμ (bp_pos (-((n:ℝ)+1))) hmass M
    simpa only [bp_neg,inv_inv] using hh
  · change pr (onW μ E) E=1
    rw [pr_on]
    have he : (fun M=>E M∧E M)=E := by funext M; exact and_self (E M)
    rw [he,div_self hpos.ne']
  · intro M hM
    have he : ¬E M := by
      intro he
      apply hM
      intro z
      change dotProduct (M none) z=0
      rw [he,zero_dotProduct]
    change onW μ E M=0
    rw [onW_val,ind_zero he,mul_zero,zero_div]

end
end Lax793645Proofs.Simplifications
