/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassIntegralBaseChange
public import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-!
# The original cubic coefficient morphism is a faithfully flat cover

The proved coefficient square transfers flatness, surjectivity and
quasi-compactness from the field extension to the actual cubic projection.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.WeierstrassIntegralChart

variable {K L : Type} [Field K] [Field L] [Algebra K L]
  (E : WeierstrassCurve K)

/-- The actual cubic projection along a field extension is flat. -/
instance integralCoefficientMorphism_field_flat :
    Flat (integralCoefficientMorphism (S := L) E) := by
  have h := (flat_and_surjective_SpecMap_iff
    (CommRingCat.ofHom (algebraMap K L))).mpr
      (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)
  exact MorphismProperty.of_isPullback (integralCoefficient_isPullback E).flip h.1

/-- Every original cubic point is covered by the actual coefficient extension. -/
instance integralCoefficientMorphism_field_surjective :
    Surjective (integralCoefficientMorphism (S := L) E) := by
  have h := (flat_and_surjective_SpecMap_iff
    (CommRingCat.ofHom (algebraMap K L))).mpr
      (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)
  exact MorphismProperty.of_isPullback (integralCoefficient_isPullback E).flip h.2

/-- The actual coefficient projection is quasi-compact. -/
instance integralCoefficientMorphism_field_quasiCompact :
    QuasiCompact (integralCoefficientMorphism (S := L) E) :=
  MorphismProperty.of_isPullback (integralCoefficient_isPullback E).flip
    (inferInstanceAs (QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap K L)))))

/-- Compatible morphisms descend uniquely through the original cubic projection. -/
instance integralCoefficientMorphism_field_effectiveEpi :
    EffectiveEpi (integralCoefficientMorphism (S := L) E) := inferInstance

end FLT.Mazur.WeierstrassIntegralChart
