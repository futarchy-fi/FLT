/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertPolynomialSchemeOverlap

/-!
# Global classifying morphisms for polynomial ideal families over schemes

The proved overlap equalities glue the actual local parameters. The result
is a morphism over the original coefficient spectrum, determined uniquely
by its restrictions to the canonical affine cover of the base.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open FLT.Mazur.FCurve

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

variable (R I : Type u) [CommRing R] (d : ℕ)
variable {X : Scheme.{u}} (s : X ⟶ Spec (.of R))
variable (J : (polynomialRelativeAmbient R I s).IdealSheafData)
variable (hJ : FiniteLocallyFreeDegree (J.subschemeι ≫ pullback.fst _ _) d)

/-- The actual global parameter of a finite locally free polynomial ideal family. -/
def polynomialSchemeFamilyMorphism : X ⟶ polynomialHilbertScheme R I d :=
  X.affineOpenCover.openCover.glueMorphisms
    (polynomialSchemeCoverParameter R I d s J hJ)
    (polynomialSchemeCoverParameter_agree R I d s J hJ)

/-- The glued parameter restricts to every original affine local parameter. -/
theorem polynomialSchemeFamilyMorphism_restrict (i : X.affineOpenCover.I₀) :
    X.affineOpenCover.f i ≫ polynomialSchemeFamilyMorphism R I d s J hJ =
      polynomialSchemeCoverParameter R I d s J hJ i :=
  X.affineOpenCover.openCover.ι_glueMorphisms _ _ i

/-- The constructed global parameter lies over the supplied scheme structure map. -/
theorem polynomialSchemeFamilyMorphism_over :
    polynomialSchemeFamilyMorphism R I d s J hJ ≫ polynomialHilbertStructure R I d = s := by
  apply Scheme.Cover.hom_ext X.affineOpenCover.openCover
  intro i
  change X.affineOpenCover.f i ≫
    (polynomialSchemeFamilyMorphism R I d s J hJ ≫ _) = X.affineOpenCover.f i ≫ s
  rw [← Category.assoc, polynomialSchemeFamilyMorphism_restrict,
    polynomialSchemeCoverParameter_over]

/-- The actual affine parameters uniquely determine the global classifying morphism. -/
theorem polynomialSchemeFamilyMorphism_unique (f : X ⟶ polynomialHilbertScheme R I d)
    (hf : ∀ i : X.affineOpenCover.I₀,
      X.affineOpenCover.f i ≫ f = polynomialSchemeCoverParameter R I d s J hJ i) :
    f = polynomialSchemeFamilyMorphism R I d s J hJ := by
  apply Scheme.Cover.hom_ext X.affineOpenCover.openCover
  intro i
  change X.affineOpenCover.f i ≫ f =
    X.affineOpenCover.f i ≫ polynomialSchemeFamilyMorphism R I d s J hJ
  rw [hf, polynomialSchemeFamilyMorphism_restrict]

end FLT.Mazur.HilbertChart
