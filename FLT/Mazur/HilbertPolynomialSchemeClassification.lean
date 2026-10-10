/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertPolynomialSchemeRecovery

/-!
# Polynomial Hilbert classification over arbitrary schemes

The glued polynomial Hilbert scheme represents actual ideal families of
finite locally free degree over every scheme over the coefficient spectrum.
The input contains only the full ideal and its geometric degree property;
all local parameters, gluing and inverse laws have been constructed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open FLT.Mazur.FCurve

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

variable (R I : Type u) [CommRing R] (d : ℕ)
variable {X : Scheme.{u}} (s : X ⟶ Spec (.of R))

/-- Actual polynomial ideal families whose closed projection has finite locally free degree. -/
def PolynomialSchemeFamilies :=
  { J : (polynomialRelativeAmbient R I s).IdealSheafData //
    FiniteLocallyFreeDegree (J.subschemeι ≫ pullback.fst _ _) d }

/-- All scheme parameters over the original coefficient spectrum. -/
def PolynomialSchemeParameters :=
  { f : X ⟶ polynomialHilbertScheme R I d // f ≫ polynomialHilbertStructure R I d = s }

/-- The actual universal closed family of a scheme parameter. -/
def polynomialSchemeParameterFamily (f : PolynomialSchemeParameters R I d s) :
    PolynomialSchemeFamilies R I d s :=
  ⟨polynomialSchemeParameterIdeal R I d s f.val f.property,
    polynomialSchemeParameterIdeal_degree R I d s f.val f.property⟩

/-- The constructed global parameter of an arbitrary actual scheme ideal family. -/
def polynomialSchemeFamilyParameter (J : PolynomialSchemeFamilies R I d s) :
    PolynomialSchemeParameters R I d s :=
  ⟨polynomialSchemeFamilyMorphism R I d s J.val J.property,
    polynomialSchemeFamilyMorphism_over R I d s J.val J.property⟩

/-- Classifying and then pulling back returns the entire supplied scheme ideal family. -/
theorem polynomialSchemeParameterFamily_familyParameter
    (J : PolynomialSchemeFamilies R I d s) :
    polynomialSchemeParameterFamily R I d s (polynomialSchemeFamilyParameter R I d s J) = J := by
  apply Subtype.ext
  exact polynomialSchemeParameterIdeal_family R I d s J.val J.property

/-- Pulling back and then classifying returns every original scheme parameter. -/
theorem polynomialSchemeFamilyParameter_parameterFamily
    (f : PolynomialSchemeParameters R I d s) :
    polynomialSchemeFamilyParameter R I d s (polynomialSchemeParameterFamily R I d s f) = f := by
  apply Subtype.ext
  exact polynomialSchemeFamilyMorphism_parameter R I d s f.val f.property

/-- The representing equivalence for polynomial ideal families over every scheme base. -/
def polynomialSchemeClassification :
    PolynomialSchemeParameters R I d s ≃ PolynomialSchemeFamilies R I d s where
  toFun := polynomialSchemeParameterFamily R I d s
  invFun := polynomialSchemeFamilyParameter R I d s
  left_inv := polynomialSchemeFamilyParameter_parameterFamily R I d s
  right_inv := polynomialSchemeParameterFamily_familyParameter R I d s

/-- The equivalence records the full actual universal pullback ideal. -/
theorem polynomialSchemeClassification_ideal (f : PolynomialSchemeParameters R I d s) :
    (polynomialSchemeClassification R I d s f).val =
      polynomialSchemeParameterIdeal R I d s f.val f.property := rfl

end FLT.Mazur.HilbertChart
