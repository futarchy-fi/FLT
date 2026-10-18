/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicAffineEquation
public import FLT.Mazur.WeierstrassGeneralizedPointedComparison
public import Mathlib.CategoryTheory.Conj

/-!
# The full comparison scheme on affine normalized chart products

For any affine map into a pair of normalized characteristic charts, the
constructed equation comparison scheme classifies every full generalized
curve comparison on every affine test algebra. No marking is fixed.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry WeierstrassCurve
namespace FLT.Mazur.CyclicCharacteristicAtlas
open WeierstrassIntegralChart WeierstrassChangeParameter GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] {A : Type} [CommRing A]
  (b c : Bool) (q : Spec (.of A) ⟶ normalizedLocus n b)
  (r : Spec (.of A) ⟶ normalizedLocus n c)

/-- The actual varying comparison scheme over an affine normalized chart product. -/
def affineComparisonScheme : Scheme :=
  comparisonScheme (affineEquation n b q) (affineEquation n c r)

/-- The varying comparison parameter retains the affine chart-product base. -/
def affineComparisonStructure : affineComparisonScheme n b c q r ⟶ Spec (.of A) :=
  comparisonStructure (affineEquation n b q) (affineEquation n c r)

variable (B : Type) [CommRing B] [Algebra A B]

/-- The specialized equation gives the original normalized family on an affine test. -/
def affineTestEquationIso :
    integralGeneralizedEllipticCurve ((affineEquation n b q).map (algebraMap A B))
        (coefficientEquation_discriminant _ (affineEquation_discriminant n b q) _) ≅
      (normalizedCurve n b).baseChange (Spec.algebraMap A B ≫ q) :=
  coefficientModelIso _ (affineEquation_discriminant n b q) (algebraMap A B) ≪≫
    (baseChangeFunctor (Spec.algebraMap A B)).mapIso (affineEquationIso n b q) ≪≫
    ((normalizedCurve n b).baseChangeCompIso q (Spec.algebraMap A B)).symm

/-- Every full original comparison has exactly one affine comparison parameter. -/
def affineComparisonPointEquiv :
    {f : Spec (.of B) ⟶ affineComparisonScheme n b c q r //
      f ≫ affineComparisonStructure n b c q r = Spec.algebraMap A B} ≃
    ((normalizedCurve n b).baseChange (Spec.algebraMap A B ≫ q) ≅
      (normalizedCurve n c).baseChange (Spec.algebraMap A B ≫ r)) :=
  (fullComparisonSchemePointEquiv _ _ (affineEquation_discriminant n b q)
      (affineEquation_discriminant n c r) B).trans
    ((generalizedPointedEquiv _ _
      (coefficientEquation_discriminant _ (affineEquation_discriminant n b q) _)
      (coefficientEquation_discriminant _ (affineEquation_discriminant n c r) _)).symm.trans
        (Iso.isoCongr (affineTestEquationIso n b q B) (affineTestEquationIso n c r B)))

/-- Classification retains each specified full comparison, including all its automorphisms. -/
theorem affineComparisonPoint_unique
    (e : (normalizedCurve n b).baseChange (Spec.algebraMap A B ≫ q) ≅
      (normalizedCurve n c).baseChange (Spec.algebraMap A B ≫ r)) :
    ∃! f : {f : Spec (.of B) ⟶ affineComparisonScheme n b c q r //
      f ≫ affineComparisonStructure n b c q r = Spec.algebraMap A B},
      affineComparisonPointEquiv n b c q r B f = e :=
  (affineComparisonPointEquiv n b c q r B).bijective.existsUnique e

end FLT.Mazur.CyclicCharacteristicAtlas
