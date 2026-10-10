/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AmbientQuotientSchemeFamilies
public import FLT.Mazur.HilbertAmbientSchemeParameters

/-!
# Hilbert representation for arbitrary affine quotient ambient schemes

The constructed closed parameter scheme classifies all actual finite locally
free ideal families in the base change of Spec of the original polynomial
quotient ring. This holds over arbitrary scheme bases, with both inverse laws
and no local bases, gluing witnesses, or ambient factorization in the input.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

variable (R I : Type u) [CommRing R] (d : ℕ)
variable (K : Ideal (MvPolynomial I R))
variable {X : Scheme.{u}} (s : X ⟶ Spec (.of R))

/-- Polynomial classification restricts to precisely the full containing families. -/
def containedPolynomialSchemeClassification :
    ContainedPolynomialSchemeParameters R I d K s ≃
      ContainedPolynomialSchemeFamilies R I d K s where
  toFun f := ⟨polynomialSchemeParameterFamily R I d s f.val, f.property⟩
  invFun J := ⟨polynomialSchemeFamilyParameter R I d s J.val, by
    change (quotientRelativeImmersion R I K s).ker ≤
      polynomialSchemeParameterIdeal R I d s
        (polynomialSchemeFamilyMorphism R I d s J.val.val J.val.property) _
    rw [polynomialSchemeParameterIdeal_family]
    exact J.property⟩
  left_inv f := Subtype.ext
    (polynomialSchemeFamilyParameter_parameterFamily R I d s f.val)
  right_inv J := Subtype.ext
    (polynomialSchemeParameterFamily_familyParameter R I d s J.val)

/-- The ambient Hilbert scheme represents all finite locally free quotient-ambient families. -/
def ambientSchemeClassification :
    AmbientSchemeParameters R I d K s ≃ QuotientSchemeFamilies R I d K s :=
  (ambientSchemeParameterEquiv R I d K s).trans
    ((containedPolynomialSchemeClassification R I d K s).trans
      (quotientSchemeFamilyCorrespondence R I d K s).symm)

/-- The universal family retains its full actual ideal in the quotient ambient base change. -/
theorem ambientSchemeClassification_ideal (f : AmbientSchemeParameters R I d K s) :
    (ambientSchemeClassification R I d K s f).val =
      (polynomialSchemeParameterIdeal R I d s (ambientSchemeForget R I d K s f).val
        (ambientSchemeForget R I d K s f).property).comap (quotientRelativeImmersion R I K s) :=
  rfl

/-- Classifying and pulling back recovers the entire original quotient-ambient family. -/
theorem ambientSchemeClassification_recovery (J : QuotientSchemeFamilies R I d K s) :
    ambientSchemeClassification R I d K s ((ambientSchemeClassification R I d K s).symm J) = J :=
  Equiv.apply_symm_apply _ J

/-- Pulling back and classifying recovers the original actual scheme parameter. -/
theorem ambientSchemeClassification_parameter (f : AmbientSchemeParameters R I d K s) :
    (ambientSchemeClassification R I d K s).symm (ambientSchemeClassification R I d K s f) = f :=
  Equiv.symm_apply_apply _ f

end FLT.Mazur.HilbertChart
