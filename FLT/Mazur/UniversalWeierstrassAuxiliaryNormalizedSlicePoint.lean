/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassAuxiliaryNormalizedPointSections
public import FLT.Mazur.UniversalWeierstrassNormalizedSliceFunctor

/-!
# Actual affine auxiliary families normalize into the original closed slice

The actual normalized level-four morphism satisfies the four frame equations
on its original coordinate functions. It therefore factors uniquely through
the constructed closed slice, retaining every label and its coefficient map.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.UniversalWeierstrass

variable {R : Type} [CommRing R] (f : Spec (.of R) ⟶ levelFour.left)

/-- The actual normalized auxiliary point satisfies every original slice relation. -/
theorem auxiliaryFamilyNormalizedPoint_satisfies :
    SatisfiesNormalization (auxiliaryPointSections (auxiliaryFamilyNormalizedPoint f)) := by
  intro i
  fin_cases i
  · change auxiliaryPointSections (auxiliaryFamilyNormalizedPoint f)
      (auxiliaryCoordinate frameLabelFirst frameLabelFirst_ne 0) = 0
    rw [auxiliaryFamilyNormalizedPoint_coordinate]
    exact (auxiliaryNormalizedEvaluation_first (auxiliaryPointSections f)).1
  · change auxiliaryPointSections (auxiliaryFamilyNormalizedPoint f)
      (auxiliaryCoordinate frameLabelFirst frameLabelFirst_ne 1) = 0
    rw [auxiliaryFamilyNormalizedPoint_coordinate]
    exact (auxiliaryNormalizedEvaluation_first (auxiliaryPointSections f)).2
  · change auxiliaryPointSections (auxiliaryFamilyNormalizedPoint f)
      (auxiliaryCoordinate frameLabelThird frameLabelThird_ne 1) = 0
    rw [auxiliaryFamilyNormalizedPoint_coordinate]
    exact (auxiliaryNormalizedEvaluation_third (auxiliaryPointSections f)).2
  · change auxiliaryPointSections (auxiliaryFamilyNormalizedPoint f)
      (auxiliaryCoordinate frameLabelThird frameLabelThird_ne 0 -
        auxiliaryCoordinate frameLabelFirst⁻¹ (inv_ne_one.mpr frameLabelFirst_ne) 1) = 0
    rw [map_sub, auxiliaryFamilyNormalizedPoint_coordinate,
      auxiliaryFamilyNormalizedPoint_coordinate, sub_eq_zero]
    exact (auxiliaryNormalizedEvaluation_third (auxiliaryPointSections f)).1.trans
      (auxiliaryNormalizedEvaluation_inverse (auxiliaryPointSections f)).2.symm

/-- The four equations vanish in the actual global sections of the source scheme. -/
theorem auxiliaryFamilyNormalizedPoint_appTop_satisfies :
    SatisfiesNormalization (auxiliaryFamilyNormalizedPoint f).appTop.hom := by
  intro i
  apply (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv.injective
  change auxiliaryPointSections (auxiliaryFamilyNormalizedPoint f)
    (normalizedSliceRelation i) = (Scheme.ΓSpecIso (.of R)).hom.hom 0
  rw [map_zero]
  exact auxiliaryFamilyNormalizedPoint_satisfies f i

/-- An actual affine auxiliary family gives an actual point of the original normalized slice. -/
def auxiliaryFamilyNormalizedSlicePoint : Spec (.of R) ⟶ normalizedSlice :=
  normalizedSliceFamilyLift (auxiliaryFamilyNormalizedPoint f)
    (auxiliaryFamilyNormalizedPoint_appTop_satisfies f)

/-- The slice point retains the entire represented normalized auxiliary family. -/
@[reassoc] theorem auxiliaryFamilyNormalizedSlicePoint_inclusion :
    auxiliaryFamilyNormalizedSlicePoint f ≫ normalizedSliceInclusion =
      auxiliaryFamilyNormalizedPoint f := normalizedSliceFamilyLift_inclusion _ _

/-- The slice point retains exactly the normalized coefficient parameter. -/
@[reassoc] theorem auxiliaryFamilyNormalizedSlicePoint_base :
    auxiliaryFamilyNormalizedSlicePoint f ≫ normalizedSliceInclusion ≫ levelFour.hom =
      auxiliaryNormalizedCoefficientBase (auxiliaryPointSections f) := by
  rw [← Category.assoc, auxiliaryFamilyNormalizedSlicePoint_inclusion,
    auxiliaryFamilyNormalizedPoint_base]

/-- Factoring this normalized family through the original slice is unique. -/
theorem auxiliaryFamilyNormalizedSlicePoint_unique (l : Spec (.of R) ⟶ normalizedSlice)
    (hl : l ≫ normalizedSliceInclusion = auxiliaryFamilyNormalizedPoint f) :
    l = auxiliaryFamilyNormalizedSlicePoint f :=
  (cancel_mono normalizedSliceInclusion).mp
    (hl.trans (auxiliaryFamilyNormalizedSlicePoint_inclusion f).symm)

end FLT.Mazur.UniversalWeierstrass
