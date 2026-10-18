/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassUniversalComparisonSpecialization
public import Mathlib.CategoryTheory.Conj

/-!
# The affine classifier is pullback of the actual universal comparison

The parameter equivalence retains the specified full comparison on every
affine test. Its value is identified with the universal family's pullback.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry WeierstrassCurve
namespace FLT.Mazur.WeierstrassChangeParameter
open WeierstrassIntegralChart GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A]
  (W V : WeierstrassCurve R) (hW : IsUnit W.Δ) (hV : IsUnit V.Δ)
  (f : {f : Spec (.of A) ⟶ comparisonScheme W V //
    f ≫ comparisonStructure W V = Spec.algebraMap R A})

/-- Extracting an algebra parameter retains the exact original scheme-test map. -/
theorem comparisonTest_spec :
    Spec.map (CommRingCat.ofHom (Spec.homEquivAlgHom f).toRingHom) = f.val :=
  Spec.map_preimage f.val

/-- Pull back the universal comparison along the specified actual affine test map. -/
def universalComparisonOnTest :
    (integralGeneralizedEllipticCurve W hW).baseChange (Spec.algebraMap R A) ≅
      (integralGeneralizedEllipticCurve V hV).baseChange (Spec.algebraMap R A) :=
  comparisonPullback _ _ (comparisonStructure W V) f.val (Spec.algebraMap R A)
    f.property.symm (universalGeneralizedComparison W V hW hV)

/-- The algebraic and geometric pullbacks use the same actual parameter morphism. -/
theorem universalComparisonOnTest_eq :
    universalComparisonOnTest W V hW hV f =
      universalComparisonOnAlgebra W V hW hV (Spec.homEquivAlgHom f) := by
  unfold universalComparisonOnTest universalComparisonOnAlgebra
  congr 1
  exact (comparisonTest_spec W V f).symm

/-- The parameter equivalence for the original full coefficient-pullback models. -/
def generalizedComparisonPointEquiv :
    {f : Spec (.of A) ⟶ comparisonScheme W V //
      f ≫ comparisonStructure W V = Spec.algebraMap R A} ≃
    ((integralGeneralizedEllipticCurve W hW).baseChange (Spec.algebraMap R A) ≅
      (integralGeneralizedEllipticCurve V hV).baseChange (Spec.algebraMap R A)) :=
  (fullComparisonSchemePointEquiv W V hW hV A).trans
    ((generalizedPointedEquiv _ _ (coefficientEquation_discriminant W hW _)
      (coefficientEquation_discriminant V hV _)).symm.trans
        (Iso.isoCongr (coefficientModelIso W hW (algebraMap R A))
          (coefficientModelIso V hV (algebraMap R A))))

/-- The pointwise classifier is precisely pullback of the actual universal full comparison. -/
theorem generalizedComparisonPointEquiv_apply :
    generalizedComparisonPointEquiv W V hW hV f =
      universalComparisonOnTest W V hW hV f := by
  rw [universalComparisonOnTest_eq, universalComparisonOnAlgebra_eq,
    changeBaseGeneralizedIso_eq]
  rfl

/-- Every full comparison occurs as the universal pullback along exactly one actual test map. -/
theorem universalComparisonOnTest_unique
    (e : (integralGeneralizedEllipticCurve W hW).baseChange (Spec.algebraMap R A) ≅
      (integralGeneralizedEllipticCurve V hV).baseChange (Spec.algebraMap R A)) :
    ∃! f : {f : Spec (.of A) ⟶ comparisonScheme W V //
      f ≫ comparisonStructure W V = Spec.algebraMap R A},
      universalComparisonOnTest W V hW hV f = e := by
  simpa only [← generalizedComparisonPointEquiv_apply] using
    (generalizedComparisonPointEquiv W V hW hV).bijective.existsUnique e

end FLT.Mazur.WeierstrassChangeParameter
