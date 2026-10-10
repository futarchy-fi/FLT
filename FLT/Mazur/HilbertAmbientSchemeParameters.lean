/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertAmbientSchemeFactorization
public import FLT.Mazur.HilbertPolynomialSchemeClassification

/-!
# All scheme parameters of the actual closed ambient Hilbert scheme

Actual maps to the constructed closed scheme correspond exactly to polynomial
parameters whose full families lie in the quotient ambient space. The inverse
is the constructed global lift, and monicity proves both inverse laws.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

variable (R I : Type u) [CommRing R] (d : ℕ)
variable (K : Ideal (MvPolynomial I R))
variable {X : Scheme.{u}} (s : X ⟶ Spec (.of R))

/-- Actual morphisms to the constructed ambient parameter scheme over the coefficient base. -/
def AmbientSchemeParameters :=
  { f : X ⟶ ambientHilbertScheme R I d K // f ≫ ambientHilbertStructure R I d K = s }

/-- Polynomial parameters whose actual full ideal families lie inside the quotient ambient. -/
def ContainedPolynomialSchemeParameters :=
  { f : PolynomialSchemeParameters R I d s // (quotientRelativeImmersion R I K s).ker ≤
    polynomialSchemeParameterIdeal R I d s f.val f.property }

/-- The polynomial parameter underlying an actual closed ambient parameter. -/
def ambientSchemeForget (f : AmbientSchemeParameters R I d K s) :
    PolynomialSchemeParameters R I d s :=
  ⟨f.val ≫ ambientHilbertι R I d K, by
    rw [Category.assoc]
    exact f.property⟩

/-- Every actual ambient parameter has its full universal family in the actual quotient ambient. -/
theorem ambientSchemeForget_contained (f : AmbientSchemeParameters R I d K s) :
    (quotientRelativeImmersion R I K s).ker ≤ polynomialSchemeParameterIdeal R I d s
      (ambientSchemeForget R I d K s f).val (ambientSchemeForget R I d K s f).property := by
  apply (ambientHilbertIdeal_eq_bot_iff R I d K s _ _).mp
  apply le_bot_iff.mp
  apply Scheme.IdealSheafData.le_map_iff_comap_le.mp
  rw [Scheme.IdealSheafData.map_bot]
  exact Scheme.Hom.le_ker_comp _ _

/-- The constructed lift of every contained polynomial parameter. -/
def containedParameterLift (f : ContainedPolynomialSchemeParameters R I d K s) :
    AmbientSchemeParameters R I d K s :=
  ⟨ambientSchemeParameterLift R I d K s f.val.val f.val.property f.property,
    ambientSchemeParameterLift_over R I d K s f.val.val f.val.property f.property⟩

/-- The actual closed ambient parameter scheme represents precisely the contained parameters. -/
def ambientSchemeParameterEquiv :
    AmbientSchemeParameters R I d K s ≃ ContainedPolynomialSchemeParameters R I d K s where
  toFun f := ⟨ambientSchemeForget R I d K s f, ambientSchemeForget_contained R I d K s f⟩
  invFun := containedParameterLift R I d K s
  left_inv f := by
    apply Subtype.ext
    apply (cancel_mono (ambientHilbertι R I d K)).mp
    exact ambientSchemeParameterLift_ι R I d K s
      (ambientSchemeForget R I d K s f).val (ambientSchemeForget R I d K s f).property
      (ambientSchemeForget_contained R I d K s f)
  right_inv f := by
    apply Subtype.ext
    apply Subtype.ext
    exact ambientSchemeParameterLift_ι R I d K s f.val.val f.val.property f.property

end FLT.Mazur.HilbertChart
