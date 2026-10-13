/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearInitialProjectiveDescent
public import FLT.Mazur.WeierstrassProjectiveFiberDescentStructure
public import FLT.Mazur.WeierstrassModificationXFullFiberProjectiveDescent

/-!
# The original initial projective descent preserves its coefficient structure

The full initial atlas equation receives the two original branches and exterior
using just their actual endpoint identifications, with the original slope normalization.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Polynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {R : Type u} [CommRing R]
  {W : WeierstrassCurve R} {π : R} {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [Field S] [Algebra R S] (r : S) (j : ℕ) (hj : j ≤ n)
  (hs : algebraMap R S (π ^ start) = 0)
  (h3 : algebraMap R S (Data.b3 (data ⟨0, Nat.zero_lt_succ n⟩)) = 0)
  (h4 : algebraMap R S (Data.b4 (data ⟨0, Nat.zero_lt_succ n⟩)) = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
local notation "a" => (rootShearCurve (W.map (algebraMap R S)) r).a₁
local notation "c" => algebraMap R S (data ⟨0, Nat.zero_lt_succ n⟩).b6
local notation "E" => coefficientShearInitialEquationIso data S r j hj hs h3 h4 hr

variable (ha : IsUnit (rootShearCurve (W.map (algebraMap R S)) r).a₁)
  (hc : algebraMap R S (data ⟨0, Nat.zero_lt_succ n⟩).b6 = 0)
  {Y : Scheme.{u}} (f₁ f₂ g : ProjectiveLine.scheme S ⟶ Y)
  (w₁ : ProjectiveLine.zero S ≫ f₁ = ProjectiveLine.zero S ≫ g)
  (w₂ : ProjectiveLine.zero S ≫ f₂ = ProjectiveLine.infinity S ≫ g)
local notation "u" => Units.mk0 a ha.ne_zero
local notation "Z" => conicZeroAffineIso c hc
local notation "p₁" => (conicFirstParameterIso a c ha).inv ≫ conicFirstOpenImmersion a c
local notation "p₂" => (conicSecondParameterIso a c ha).inv ≫ conicSecondOpenImmersion a c

variable (p : Y ⟶ Spec (.of S))
  (hf₁ : f₁ ≫ p = ProjectiveLine.toBase S)
  (hf₂ : f₂ ≫ p = ProjectiveLine.toBase S)
  (hg : g ≫ p = ProjectiveLine.toBase S)

include hf₁ hf₂ hg in
/-- The whole original initial equation descends over the coefficient field. -/
theorem coefficientShearInitialProjectiveDesc_structure :
    coefficientShearInitialProjectiveDesc
      data S r j hj hs h3 h4 hr ha hc f₁ f₂ g w₁ w₂ ≫ p =
        coefficientShearAtlasStructure data S r j hj (.inl 2) := by
  apply (cancel_epi (E).hom).mp
  rw [coefficientShearInitialProjectiveDesc_normal_assoc,
    fullFiberProjectiveDesc_structure c hc f₁ f₂ p hf₁ hf₂ u g w₁ w₂ hg]
  exact (terminalComponent_algebra_structure
    (coefficientShearNormalEquiv W (π ^ start)
      (data ⟨0, Nat.zero_lt_succ n⟩).b3 (data ⟨0, Nat.zero_lt_succ n⟩).b4
      (data ⟨0, Nat.zero_lt_succ n⟩).b6 S r hs h3 h4 hr).toAlgHom).symm

end FLT.Mazur.WeierstrassDividedDepth
