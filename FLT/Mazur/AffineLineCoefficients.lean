/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffinePicardSections
public import FLT.Mazur.AffineGeometricDescent

/-!
# Invertible coordinate modules of affine line bundles

The coordinate-ring tensor comparison carries the dual evaluation of a line
bundle to a tensor inverse of its actual affine coefficient module. This
supplies the coefficient hypothesis required by effective geometric descent.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.AffineGeometricDescent
open FCurve FCurve.ModuleSheafTensor AffineOverlapPullback
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R S : CommRingCat.{u}}

/-- The structure module's coordinate coefficients recover the coordinate ring. -/
def structureCoefficientsIso : coefficients R (structureModule (Spec R)) ≅ ModuleCat.of R R :=
  (moduleSpecΓFunctor.mapIso tildeSelf).symm ≪≫ (tilde.isoTop (ModuleCat.of R R)).symm

/-- An actual affine line bundle has invertible coefficients over its coordinate ring. -/
theorem coefficients_invertible (M : (Spec S).Modules) (hM : LocallyFreeRankOne M) :
    Module.Invertible S (coefficients S M) := by
  have := SchemePicard.rankOne_finitePresentation M hM
  have := SchemePicard.rankOne_finitePresentation _ hM.dual
  exact Module.Invertible.right
    ((asIso (affineUnit (moduleSheafDual M) M) ≪≫
      moduleSpecΓFunctor.mapIso (lineSheafDualEvaluationIso hM) ≪≫
      structureCoefficientsIso).toLinearEquiv)

/-- Effective geometric descent preserves the actual local rank-one property. -/
theorem descendedSheaf_line (φ : R ⟶ S) (M : (Spec S).Modules)
    [M.IsQuasicoherent] (D : Data φ M) (hφ : φ.hom.FaithfullyFlat)
    (hM : LocallyFreeRankOne M) : LocallyFreeRankOne (descendedSheaf φ M D hφ) := by
  have := coefficients_invertible M hM
  exact descendedSheaf_locallyFreeRankOne φ M D hφ

end FLT.Mazur.AffineGeometricDescent
