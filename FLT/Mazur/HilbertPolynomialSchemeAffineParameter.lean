/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ClosedIdealCartesianDegree
public import FLT.Mazur.PolynomialAffineIdealDegree
public import FLT.Mazur.PolynomialRelativeAffineCover

/-!
# Local parameters of actual polynomial ideal families over schemes

An arbitrary affine test of a scheme base restricts the supplied ideal to
an actual polynomial spectrum. Its closed projection is cartesian, so its
coordinate quotient is classified by the affine representing equivalence.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open FLT.Mazur.BaseAdicThickening FLT.Mazur.FCurve

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

variable (R I : Type u) [CommRing R] (d : ℕ)
variable {X : Scheme.{u}} (s : X ⟶ Spec (.of R))
variable (J : (polynomialRelativeAmbient R I s).IdealSheafData)
variable (hJ : FiniteLocallyFreeDegree (J.subschemeι ≫ pullback.fst _ _) d)
variable (S : Type u) [CommRing S] [Algebra R S]
variable (a : Spec (.of S) ⟶ X)
variable (ha : a ≫ s = Spec.map (CommRingCat.ofHom (algebraMap R S)))

include hJ

/-- The full ideal restricted to any affine base test has the original degree. -/
theorem polynomialSchemeAffineIdeal_degree :
    FiniteLocallyFreeDegree
      ((J.comap (polynomialRelativeAffineChart R I s S a ha)).subschemeι ≫
        Spec.map (CommRingCat.ofHom (MvPolynomial.C (R := S) (σ := I)))) d :=
  ClosedIdealCover.restriction_degree J _
    (polynomialRelativeAffineChart_isPullback R I s S a ha) d hJ

/-- The actual coordinate quotient of every affine test is a finite flat quotient family. -/
def polynomialSchemeAffineFamily : PolynomialQuotientFamilies I d S :=
  polynomialCoordinateFamily I S d (J.comap (polynomialRelativeAffineChart R I s S a ha))
    (polynomialSchemeAffineIdeal_degree R I d s J hJ S a ha)

/-- The local parameter classifies the entire restricted ideal, with no supplied basis. -/
def polynomialSchemeAffineParameter : PolynomialHilbertParameters R I d S :=
  (polynomialAffineClassification R I d S).symm
    (polynomialSchemeAffineFamily R I d s J hJ S a ha)

/-- The local parameter recovers the full coordinate ideal of the supplied family. -/
theorem polynomialSchemeAffineParameter_ideal :
    polynomialParameterIdeal R I d S
        (polynomialSchemeAffineParameter R I d s J hJ S a ha).val
        (polynomialSchemeAffineParameter R I d s J hJ S a ha).property =
      coordinateIdeal (.of (MvPolynomial I S))
        (J.comap (polynomialRelativeAffineChart R I s S a ha)) :=
  congrArg Subtype.val ((polynomialAffineClassification R I d S).apply_symm_apply
    (polynomialSchemeAffineFamily R I d s J hJ S a ha))

/-- Sheafifying the classified ideal recovers the full restriction of the original family. -/
theorem polynomialSchemeAffineParameter_sheaf :
    baseIdeal (.of (MvPolynomial I S))
        (polynomialParameterIdeal R I d S
          (polynomialSchemeAffineParameter R I d s J hJ S a ha).val
          (polynomialSchemeAffineParameter R I d s J hJ S a ha).property) =
      J.comap (polynomialRelativeAffineChart R I s S a ha) := by
  rw [polynomialSchemeAffineParameter_ideal, baseIdeal_coordinateIdeal]

end FLT.Mazur.HilbertChart
