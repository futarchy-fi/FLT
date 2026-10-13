/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearInitialEquationDescent
public import FLT.Mazur.WeierstrassModificationXFullFiberProjectiveDescent

/-!
# Projective-component descent on the actual initial coefficient chart

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

/-- The three complete component maps descend on the actual entire initial atlas object. -/
@[irreducible] def coefficientShearInitialProjectiveDesc :
    coefficientShearAtlasObject data S r j hj (.inl 2) ⟶ Y :=
  (E).inv ≫ fullFiberProjectiveDesc u c hc f₁ f₂ g w₁ w₂

/-- The normal comparison recovers the constructed full initial fiber morphism. -/
@[reassoc] theorem coefficientShearInitialProjectiveDesc_normal :
    (E).hom ≫ coefficientShearInitialProjectiveDesc
      data S r j hj hs h3 h4 hr ha hc f₁ f₂ g w₁ w₂ =
        fullFiberProjectiveDesc u c hc f₁ f₂ g w₁ w₂ := by
  rw [coefficientShearInitialProjectiveDesc, Iso.hom_inv_id_assoc]

/-- The first actual complete affine branch receives the first projective component map. -/
@[reassoc] theorem coefficientShearInitialProjectiveDesc_first :
    (Z).hom ≫ p₁ ≫ fiberConicImmersion a c ≫ (E).hom ≫
      coefficientShearInitialProjectiveDesc data S r j hj hs h3 h4 hr ha hc f₁ f₂ g w₁ w₂ =
        ProjectiveLine.left S ≫ f₁ := by
  rw [coefficientShearInitialProjectiveDesc_normal]
  exact fullFiberProjectiveDesc_first u c hc f₁ f₂ g w₁ w₂

/-- The opposite actual complete affine branch receives its independent component map. -/
@[reassoc] theorem coefficientShearInitialProjectiveDesc_second :
    (Z).hom ≫ p₂ ≫ fiberConicImmersion a c ≫ (E).hom ≫
      coefficientShearInitialProjectiveDesc data S r j hj hs h3 h4 hr ha hc f₁ f₂ g w₁ w₂ =
        ProjectiveLine.left S ≫ f₂ := by
  rw [coefficientShearInitialProjectiveDesc_normal]
  exact fullFiberProjectiveDesc_second u c hc f₁ f₂ g w₁ w₂

/-- The entire original incidence line receives the actual normalized exterior map. -/
@[reassoc] theorem coefficientShearInitialProjectiveDesc_incidence :
    fiberIncidenceImmersion a c ≫ (E).hom ≫
      coefficientShearInitialProjectiveDesc data S r j hj hs h3 h4 hr ha hc f₁ f₂ g w₁ w₂ =
        ProjectiveLine.left S ≫ (ProjectiveLine.slopeNormalizationIso u).hom ≫ g := by
  rw [coefficientShearInitialProjectiveDesc_normal]
  exact fullFiberProjectiveDesc_incidence u c hc f₁ f₂ g w₁ w₂

end FLT.Mazur.WeierstrassDividedDepth
