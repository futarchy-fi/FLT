/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ClosedIdealAffineCoverDescent
public import FLT.Mazur.HilbertPolynomialSchemeFaithful
public import FLT.Mazur.HilbertPolynomialSchemeMorphism
public import FLT.Mazur.HilbertPolynomialSchemeParameterDegree

/-!
# Both inverse laws for polynomial families over arbitrary schemes

The full supplied ideal is recovered on the constructed polynomial ambient
cover, and affine ideal descent detects its equality globally. Faithfulness
then recovers every arbitrary scheme parameter from its universal family.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open FLT.Mazur.BaseAdicThickening FLT.Mazur.FCurve

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

variable (R I : Type u) [CommRing R] (d : ℕ)
variable {X : Scheme.{u}} (s : X ⟶ Spec (.of R))

/-- Classifying an arbitrary actual scheme ideal family recovers its full ideal. -/
theorem polynomialSchemeParameterIdeal_family
    (J : (polynomialRelativeAmbient R I s).IdealSheafData)
    (hJ : FiniteLocallyFreeDegree (J.subschemeι ≫ pullback.fst _ _) d) :
    polynomialSchemeParameterIdeal R I d s (polynomialSchemeFamilyMorphism R I d s J hJ)
        (polynomialSchemeFamilyMorphism_over R I d s J hJ) = J := by
  apply idealSheaf_ext_of_affineCover (polynomialRelativeAffineCover R I s)
  intro i
  let _ := polynomialCoverAlgebra R s i
  change (polynomialSchemeParameterIdeal R I d s _ _).comap
      (polynomialRelativeAffineChart R I s (X.affineOpenCover.X i)
        (X.affineOpenCover.f i) (polynomialCoverAlgebra_over R s i)) = _
  rw [polynomialSchemeParameterIdeal_affineTest]
  simp only [polynomialSchemeFamilyMorphism_restrict]
  exact polynomialSchemeAffineParameter_sheaf R I d s J hJ (X.affineOpenCover.X i)
    (X.affineOpenCover.f i) (polynomialCoverAlgebra_over R s i)

/-- Classifying the actual universal pullback recovers every original scheme parameter. -/
theorem polynomialSchemeFamilyMorphism_parameter
    (f : X ⟶ polynomialHilbertScheme R I d)
    (hf : f ≫ polynomialHilbertStructure R I d = s) :
    polynomialSchemeFamilyMorphism R I d s (polynomialSchemeParameterIdeal R I d s f hf)
      (polynomialSchemeParameterIdeal_degree R I d s f hf) = f := by
  apply polynomialSchemeParameterIdeal_injective R I d s _ f
    (polynomialSchemeFamilyMorphism_over R I d s _ _) hf
  exact polynomialSchemeParameterIdeal_family R I d s _ _

end FLT.Mazur.HilbertChart
