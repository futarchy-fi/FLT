/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.AlgebraicFieldExtensionReduced
public import FLT.Mazur.WeierstrassCoefficientFieldCover
public import FLT.Mazur.WeierstrassIntegralDomain
public import FLT.Mazur.WeierstrassIntegralProper

/-!
# Reducedness of the original cubic coefficient kernel pair

The original coefficient morphism is geometrically reduced. Its kernel pair
is reduced by flatness over the original reduced, locally Noetherian cubic.
This concerns the actual glued cubics and their actual coefficient projection.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.WeierstrassIntegralChart

variable {K L : Type} [Field K] [Field L] [Algebra K L]
  [CharZero K] [Algebra.IsAlgebraic K L] (E : WeierstrassCurve K)

/-- The original algebraic coefficient cover is geometrically reduced. -/
instance integralCoefficientMorphism_geometricallyReduced :
    GeometricallyReduced (integralCoefficientMorphism (S := L) E) :=
  MorphismProperty.of_isPullback (integralCoefficient_isPullback E).flip
    (inferInstanceAs (GeometricallyReduced
      (Spec.map (CommRingCat.ofHom (algebraMap K L)))))

/-- The actual kernel-pair scheme has no nilpotent structure. -/
instance integralCoefficientOverlap_isReduced :
    IsReduced (pullback (integralCoefficientMorphism (S := L) E)
      (integralCoefficientMorphism (S := L) E)) := by
  let _ : IsLocallyNoetherian (integralCurve (E.map (algebraMap K L))) :=
    LocallyOfFiniteType.isLocallyNoetherian (integralCurveStructure _)
  infer_instance

end FLT.Mazur.WeierstrassIntegralChart
