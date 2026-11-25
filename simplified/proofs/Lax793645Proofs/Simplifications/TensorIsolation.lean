import Lax793645Proofs.Simplifications.TensorConfinement

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix Submodule Module Finset
open scoped BigOperators
noncomputable section

variable {S T I : Type} [Fintype S] [Fintype T] [Fintype I]

/-- Coordinates of the protected rectangle and the selected diagonal points
in bases extending both protected spaces and the selected vectors. -/
def selectedCoordinate (a : I → S) (b : I → T) (x : S × T) : Prop :=
  ∃ i, (a i,b i)=x

def protectedOrSelected (U : Set S) (V : Set T) (a : I → S) (b : I → T)
    (x : S × T) : Prop := (x.1 ∈ U ∧ x.2 ∈ V) ∨ selectedCoordinate a b x

def protectedCross (U : Set S) (V : Set T) (x : S × T) : Prop :=
  x.1 ∈ U ∨ x.2 ∈ V

def selectedDiagonal (a : I → S) (b : I → T) (c : I → F) : Mat (S × T) (S × T) := by
  classical
  exact fun x y => ∑ q, if x=(a q,b q) ∧ y=(a q,b q) then c q else 0

theorem selectedDiagonal_row [DecidableEq S] [DecidableEq T]
    (a : I → S) (b : I → T) (c : I → F)
    (ha : Function.Injective a) (q : I) (y : S × T) :
    selectedDiagonal a b c (a q,b q) y = if y=(a q,b q) then c q else 0 := by
  classical
  unfold selectedDiagonal
  rw [Finset.sum_eq_single q]
  · simp
  · intro k _ hk
    have h : (a q,b q) ≠ (a k,b k) := by
      intro he; exact hk (ha (congrArg Prod.fst he)).symm
    simp [h]
  · simp

theorem selectedDiagonal_miss (a : I → S) (b : I → T) (c : I → F)
    (x y : S × T) (hx : ¬selectedCoordinate a b x) :
    selectedDiagonal a b c x y=0 := by
  classical
  apply Finset.sum_eq_zero
  intro q _
  simp only [if_neg (show ¬(x=(a q,b q) ∧ y=(a q,b q)) from
    fun h => hx ⟨q,h.1.symm⟩)]

theorem selectedDiagonal_sym (a : I → S) (b : I → T) (c : I → F)
    (x y : S × T) : selectedDiagonal a b c x y=selectedDiagonal a b c y x := by
  classical
  simp only [selectedDiagonal,and_comm]

theorem selectedDiagonal_sum [DecidableEq S] [DecidableEq T]
    (a : I → S) (b : I → T) (c : I → F) :
    selectedDiagonal a b c =
      ∑ q, c q • vecMulVec (Pi.single (a q,b q) 1) (Pi.single (a q,b q) 1) := by
  classical
  ext x y
  simp only [selectedDiagonal,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,vecMulVec]
  apply Finset.sum_congr rfl
  intro q _
  by_cases hx : x=(a q,b q) <;> by_cases hy : y=(a q,b q) <;> simp [hx,hy]

section Isolation
variable (w : Mat (S × T) (S × T)) (U : Set S) (V : Set T)
  (a : I → S) (b : I → T)
  (ha : Function.Injective a) (hb : Function.Injective b)
  (haU : ∀ i, a i ∉ U) (hbV : ∀ i, b i ∉ V)
  (εS : Vec S) (εT : Vec T)
  (hεS : ∀ i, εS (a i)=1) (hεT : ∀ i, εT (b i)=1)
  (hsel : ∀ c d i j, w (c,i) (d,j)=w (d,i) (c,j))
  (hbase : ∀ c d i j, w (c,i) (d,j)=w (c,j) (d,i))
  (hdiagS : ∀ c i j, w (c,i) (c,j)=∑ d, εS d*w (c,i) (d,j))
  (hdiagT : ∀ c d i, w (c,i) (d,i)=∑ j, εT j*w (c,i) (d,j))
  (hzero : ∀ x y, ¬protectedOrSelected U V a b x →
    ¬protectedOrSelected U V a b y → w x y=0)

include ha hb haU hbV in
theorem mixed_not_protected_selected (q : I) (c : S) (j : T)
    (hc : c ≠ a q) (hj : j ≠ b q) :
    ¬protectedOrSelected U V a b (a q,j) ∧
    ¬protectedOrSelected U V a b (c,b q) := by
  constructor
  · rintro (h|⟨k,hk⟩)
    · exact haU q h.1
    · have he : k=q := ha (congrArg Prod.fst hk)
      subst k
      exact hj (congrArg Prod.snd hk).symm
  · rintro (h|⟨k,hk⟩)
    · exact hbV q h.2
    · have he : k=q := hb (congrArg Prod.snd hk)
      subst k
      exact hc (congrArg Prod.fst hk).symm

include hsel hbase in
theorem separate_symmetry_total (x y : S × T) : w x y=w y x := by
  exact (hsel x.1 y.1 x.2 y.2).trans (hbase y.1 x.1 x.2 y.2)

include ha hb haU hbV hεS hεT hsel hbase hdiagS hdiagT hzero in
/-- The Boolean diagonal identities kill the entries sharing just one factor
with a selected atom. The constant functionals may have arbitrary coordinates
in the adapted bases; only their values on selected vectors are fixed. -/
theorem selected_row_isolated (q : I) (y : S × T) (hy : y ≠ (a q,b q)) :
    w (a q,b q) y=0 := by
  classical
  rcases y with ⟨c,j⟩
  by_cases hc : c=a q
  · subst c
    have hj : j ≠ b q := by intro h; exact hy (by rw [h])
    have hn : ¬protectedOrSelected U V a b (a q,j) := by
      rintro (h|⟨k,hk⟩)
      · exact haU q h.1
      have he : k=q := ha (congrArg Prod.fst hk)
      subst k
      exact hj (congrArg Prod.snd hk).symm
    have he := hdiagT (a q) (a q) j
    rw [hzero _ _ hn hn,Finset.sum_eq_single (b q)] at he
    · rw [hεT,one_mul] at he
      exact (hbase (a q) (a q) (b q) j).trans he.symm
    · intro z _ hz
      have hz' : ¬protectedOrSelected U V a b (a q,z) := by
        rintro (h|⟨k,hk⟩)
        · exact haU q h.1
        have hek : k=q := ha (congrArg Prod.fst hk)
        subst k
        exact hz (congrArg Prod.snd hk).symm
      rw [hzero _ _ hn hz',mul_zero]
    · simp
  by_cases hj : j=b q
  · subst j
    have hn : ¬protectedOrSelected U V a b (c,b q) := by
      rintro (h|⟨k,hk⟩)
      · exact hbV q h.2
      have he : k=q := hb (congrArg Prod.snd hk)
      subst k
      exact hc (congrArg Prod.fst hk).symm
    have he := hdiagS c (b q) (b q)
    rw [hzero _ _ hn hn,Finset.sum_eq_single (a q)] at he
    · rw [hεS,one_mul] at he
      exact (hsel (a q) c (b q) (b q)).trans he.symm
    · intro d _ hd
      have hd' : ¬protectedOrSelected U V a b (d,b q) := by
        rintro (h|⟨k,hk⟩)
        · exact hbV q h.2
        have hek : k=q := hb (congrArg Prod.snd hk)
        subst k
        exact hd (congrArg Prod.fst hk).symm
      rw [hzero _ _ hn hd',mul_zero]
    · simp
  obtain ⟨h1,h2⟩ := mixed_not_protected_selected U V a b ha hb haU hbV q c j hc hj
  exact (hbase (a q) c (b q) j).trans (hzero _ _ h1 h2)

include ha hb haU hbV hεS hεT hsel hbase hdiagS hdiagT hzero in
/-- Subtracting the selected diagonal atoms leaves a matrix supported on
the protected cross in both factors, the coordinate form of L tensor L. -/
theorem tensor_isolation_coordinates :
    let c := fun q => w (a q,b q) (a q,b q)
    let w₀ := w-selectedDiagonal a b c
    ∀ x y, (¬protectedCross U V x ∨ ¬protectedCross U V y) → w₀ x y=0 := by
  classical
  let c := fun q => w (a q,b q) (a q,b q)
  let w₀ := w-selectedDiagonal a b c
  have hrow (q : I) (y : S × T) : w₀ (a q,b q) y=0 := by
    change w (a q,b q) y-selectedDiagonal a b c (a q,b q) y=0
    rw [selectedDiagonal_row a b c ha]
    by_cases hy : y=(a q,b q)
    · rw [if_pos hy,hy]; exact sub_self _
    rw [if_neg hy,sub_zero]
    exact selected_row_isolated w U V a b ha hb haU hbV εS εT hεS hεT
      hsel hbase hdiagS hdiagT hzero q y hy
  have hsym (x y : S × T) : w₀ x y=w₀ y x := by
    change w x y-selectedDiagonal a b c x y=w y x-selectedDiagonal a b c y x
    rw [separate_symmetry_total w hsel hbase,selectedDiagonal_sym a b c x y]
  have hleft (x y : S × T) (hx : ¬protectedCross U V x) : w₀ x y=0 := by
    have hxS : x.1 ∉ U := fun h => hx (Or.inl h)
    have hxT : x.2 ∉ V := fun h => hx (Or.inr h)
    by_cases hs : selectedCoordinate a b x
    · obtain ⟨q,rfl⟩ := hs
      exact hrow q y
    have hn : ¬protectedOrSelected U V a b x := by
      rintro (h|h); exact hxS h.1; exact hs h
    by_cases hy : selectedCoordinate a b y
    · obtain ⟨q,rfl⟩ := hy
      exact (hsym x _).trans (hrow q x)
    change w x y-selectedDiagonal a b c x y=0
    rw [selectedDiagonal_miss a b c x y hs,sub_zero]
    by_cases hD : y.1 ∈ U ∧ y.2 ∈ V
    · rw [hbase x.1 y.1 x.2 y.2]
      apply hzero
      · rintro (h|⟨q,hq⟩)
        · exact hxS h.1
        · apply hbV q
          rw [show b q=y.2 from congrArg Prod.snd hq]
          exact hD.2
      · rintro (h|⟨q,hq⟩)
        · exact hxT h.2
        · apply haU q
          rw [show a q=y.1 from congrArg Prod.fst hq]
          exact hD.1
    exact hzero x y hn (by rintro (h|h); exact hD h; exact hy h)
  change ∀ x y, (¬protectedCross U V x ∨ ¬protectedCross U V y) → w₀ x y=0
  intro x y h
  rcases h with h|h
  · exact hleft x y h
  · exact (hsym x y).trans (hleft y x h)

end Isolation

end
end Lax793645Proofs.Simplifications
