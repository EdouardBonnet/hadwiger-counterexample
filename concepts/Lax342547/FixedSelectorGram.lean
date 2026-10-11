import Lax342547.FlavorAffineSlices

/-!
---
title: Uniform positive Gram mass from bounded tester prescriptions
type: definition and theorem
---
At a fixed selector the sharp mixer contribution vanishes. Prescribing only
retained tester pairs has mass independent of the growing free dimension.
Routing across all retained tester pairs realizes every target slice Gram.
-/

namespace Lax342547.FixedSelectorGram
noncomputable section
open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry
open Lax342547.AffineSliceIndependence Lax342547.FlavorAffineSlices Lax342547.Atoms
open scoped BigOperators ENNReal
set_option backward.isDefEq.respectTransparency false

abbrev TesterBlock (k : ℕ) := Option (Tag k × Tag k)

def testerCoordinate {k n r : ℕ} (hr : 2*r ≤ n)
    (u : TesterBlock k × Fin r × Bool) : Base k n :=
  let i := if u.2.2 then pairRight hr u.2.1 else pairLeft hr u.2.1
  match u.1 with
  | none => shared i
  | some (d,t) => ordinary d t i

def blockRetained {k : ℕ} (l : Tag k) (f : Flavor k) : TesterBlock k → Prop
  | none => match f with | .pure _ => False | _ => True
  | some (d,t) => l ∈ interval k d ∧ match f with
      | .generic => True | .sharedOnly => False | .pure blocks => (d,t) ∈ blocks

abbrev Slots {k : ℕ} (l : Tag k) (f : Flavor k) (r : ℕ) :=
  {q : TesterBlock k // blockRetained l f q} × Fin r × Bool

noncomputable instance {k : ℕ} (l : Tag k) (f : Flavor k) :
    Fintype {q : TesterBlock k // blockRetained l f q} := Fintype.ofFinite _

noncomputable instance {k r : ℕ} (l : Tag k) (f : Flavor k) : Fintype (Slots l f r) :=
  Fintype.ofFinite _

noncomputable instance {k r : ℕ} {D : Type} [Fintype D]
    (l : Tag k) (f : Flavor k) : Fintype (Matrix (Slots l f r) (Option D) Binary) := Fintype.ofFinite _

def slotIndex {k n r : ℕ} (hr : 2*r ≤ n) (l : Tag k) (f : Flavor k)
    (u : Slots l f r) : {a : Base k n // a ∈ retained l f} :=
  ⟨testerCoordinate hr (u.1.val,u.2), (show testerCoordinate hr (u.1.val,u.2) ∈ retained (n := n) l f ↔ blockRetained l f u.1.val from by
      change retained l f (testerCoordinate hr (u.1.val,u.2)) ↔ _
      cases u.1.val with
      | none => cases f <;> simp [testerCoordinate,shared,retained,blockRetained]
      | some q => cases f <;> simp [testerCoordinate,ordinary,retained,blockRetained]).mpr u.1.property⟩

def restrictTesters {k n r : ℕ} {D : Type} (hr : 2*r ≤ n) (l : Tag k) (f : Flavor k) :
    Coefficients n l f D →ₗ[Binary] Matrix (Slots l f r) (Option D) Binary where
  toFun V := fun u j => V (slotIndex hr l f u) j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def restrictedGram {k r : ℕ} {l : Tag k} {f : Flavor k} {D : Type}
    (X : Matrix (Slots l f r) (Option D) Binary) : Matrix (Option D) (Option D) Binary :=
  fun i j => ∑ q : {q : TesterBlock k // blockRetained l f q},∑ ρ : Fin r,
    X (q,ρ,false) i*X (q,ρ,true) j

abbrev Pairs {k : ℕ} (l : Tag k) (f : Flavor k) (r : ℕ) :=
  {q : TesterBlock k // blockRetained l f q} × Fin r

def routing {k r : ℕ} {l : Tag k} {f : Flavor k} {D : Type}
    (c : Option D → Pairs l f r) (G : Matrix (Option D) (Option D) Binary) :
    Matrix (Slots l f r) (Option D) Binary := by
  classical
  exact fun u j => if u.2.2 then Function.extend c (fun i => G i j) 0 (u.1,u.2.1)
    else if (u.1,u.2.1) = c j then 1 else 0

def massFloor {k : ℕ} (l : Tag k) (f : Flavor k) (r : ℕ) (D : Type) [Fintype D] : ℝ :=
  1/(2 : ℝ)^(Fintype.card (Slots l f r)*Fintype.card (Option D))

axiom same_selector_gram {k n b degree r : ℕ} {D : Type}
    (hr : 2*r ≤ n) (hd : 1 ≤ degree)
    (M : Fin b → Matrix (Fin n) (Fin n) Binary) (s : Fin b → Binary)
    (V W : Matrix (Base k n) (Option D) Binary) :
    (pointColumns s V).transpose*selfGram hr hd M*pointColumns s W =
      fun i j => (∑ d : Tag k,∑ t : Tag k,∑ ρ : Fin r,
        V (ordinary d t (pairLeft hr ρ)) i*W (ordinary d t (pairRight hr ρ)) j)+
        ∑ ρ : Fin r,V (shared (pairLeft hr ρ)) i*W (shared (pairRight hr ρ)) j

axiom restriction_uniform {k n r : ℕ} {D : Type} [Fintype D]
    (hr : 2*r ≤ n) (l : Tag k) (f : Flavor k) :
    (PMF.uniformOfFintype (Coefficients n l f D)).map (restrictTesters hr l f) =
      PMF.uniformOfFintype (Matrix (Slots l f r) (Option D) Binary)

axiom prescription_mass {k n r : ℕ} {D : Type} [Fintype D]
    (hr : 2*r ≤ n) (l : Tag k) (f : Flavor k)
    (X : Matrix (Slots l f r) (Option D) Binary) :
    (PMF.uniformOfFintype (Coefficients n l f D)).toOuterMeasure
      {V | restrictTesters hr l f V = X} =
        1/(2 : ℝ≥0∞)^(Fintype.card (Slots l f r)*Fintype.card (Option D))

axiom gram_restriction {k n b degree r : ℕ} {D : Type}
    (hr : 2*r ≤ n) (hd : 1 ≤ degree)
    (M : Fin b → Matrix (Fin n) (Fin n) Binary) (s : Fin b → Binary)
    (l : Tag k) (f : Flavor k) (V : Coefficients n l f D) :
    (pointColumns s (value V)).transpose*selfGram hr hd M*pointColumns s (value V) =
      restrictedGram (restrictTesters hr l f V)

axiom routed_gram {k r : ℕ} {l : Tag k} {f : Flavor k} {D : Type}
    [Fintype D]
    (c : Option D → Pairs l f r) (hc : Function.Injective c)
    (G : Matrix (Option D) (Option D) Binary) : restrictedGram (routing c G) = G

axiom gram_mass_bound {k n b degree r : ℕ} {D : Type} [Fintype D]
    (hr : 2*r ≤ n) (hd : 1 ≤ degree)
    (M : Fin b → Matrix (Fin n) (Fin n) Binary) (s : Fin b → Binary)
    (l : Tag k) (f : Flavor k)
    (c : Option D → Pairs l f r) (hc : Function.Injective c)
    (G : Matrix (Option D) (Option D) Binary) :
    1/(2 : ℝ≥0∞)^(Fintype.card (Slots l f r)*Fintype.card (Option D)) ≤
      (PMF.uniformOfFintype (Coefficients n l f D)).toOuterMeasure
        {V | (pointColumns s (value V)).transpose*selfGram hr hd M*pointColumns s (value V) = G}

axiom positive_gram_mass {k n b degree r : ℕ} {D : Type} [Fintype D]
    (hr : 2*r ≤ n) (hd : 1 ≤ degree)
    (M : Fin b → Matrix (Fin n) (Fin n) Binary) (s : Fin b → Binary)
    (l : Tag k) (f : Flavor k)
    (hroom : Fintype.card (Option D) ≤ Fintype.card (Pairs l f r))
    (G : Matrix (Option D) (Option D) Binary) :
    1/(2 : ℝ≥0∞)^(Fintype.card (Slots l f r)*Fintype.card (Option D)) ≤
      (PMF.uniformOfFintype (Coefficients n l f D)).toOuterMeasure
        {V | (pointColumns s (value V)).transpose*selfGram hr hd M*pointColumns s (value V) = G}

axiom massFloor_pos {k : ℕ} (l : Tag k) (f : Flavor k) (r : ℕ) (D : Type) [Fintype D] :
    0 < massFloor l f r D

axiom gram_cell_mass {k n b degree r : ℕ} {D : Type} [Fintype D]
    (hr : 2*r ≤ n) (hd : 1 ≤ degree)
    (M : Fin b → Matrix (Fin n) (Fin n) Binary) (s : Fin b → Binary)
    (l : Tag k) (f : Flavor k)
    (hroom : Fintype.card (Option D) ≤ Fintype.card (Pairs l f r))
    (G : Matrix (Option D) (Option D) Binary) :
    massFloor l f r D ≤ Lax342547.RetainedImages.cellMass
      (Lax342547.RealCellLaws.weights (PMF.uniformOfFintype (Coefficients n l f D)))
      (fun V => (pointColumns s (value V)).transpose*selfGram hr hd M*pointColumns s (value V) = G)

end
end Lax342547.FixedSelectorGram
