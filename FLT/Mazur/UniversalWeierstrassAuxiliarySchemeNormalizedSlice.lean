/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassAuxiliarySchemeNormalizedCoordinates
public import FLT.Mazur.UniversalWeierstrassNormalizedSliceFunctor

/-!
# Arbitrary auxiliary scheme families normalize into the original closed slice

The actual normalized level-four morphism satisfies the four frame equations
on its original coordinate functions. It therefore factors uniquely through
the constructed closed slice, retaining every label and its coefficient map.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.UniversalWeierstrass

variable {T : Scheme} (f : T ⟶ levelFour.left)

/-- The actual normalized auxiliary point satisfies every original slice relation. -/
theorem auxiliarySchemeNormalizedPoint_satisfies :
    SatisfiesNormalization ((auxiliarySchemeNormalizedPoint f).appTop.hom) := by
  intro i
  fin_cases i
  · change (auxiliarySchemeNormalizedPoint f).appTop.hom
      (auxiliaryCoordinate frameLabelFirst frameLabelFirst_ne 0) = 0
    rw [auxiliarySchemeNormalizedPoint_coordinate]
    exact (auxiliaryNormalizedEvaluation_first f.appTop.hom).1
  · change (auxiliarySchemeNormalizedPoint f).appTop.hom
      (auxiliaryCoordinate frameLabelFirst frameLabelFirst_ne 1) = 0
    rw [auxiliarySchemeNormalizedPoint_coordinate]
    exact (auxiliaryNormalizedEvaluation_first f.appTop.hom).2
  · change (auxiliarySchemeNormalizedPoint f).appTop.hom
      (auxiliaryCoordinate frameLabelThird frameLabelThird_ne 1) = 0
    rw [auxiliarySchemeNormalizedPoint_coordinate]
    exact (auxiliaryNormalizedEvaluation_third f.appTop.hom).2
  · change (auxiliarySchemeNormalizedPoint f).appTop.hom
      (auxiliaryCoordinate frameLabelThird frameLabelThird_ne 0 -
        auxiliaryCoordinate frameLabelFirst⁻¹ (inv_ne_one.mpr frameLabelFirst_ne) 1) = 0
    rw [map_sub, auxiliarySchemeNormalizedPoint_coordinate,
      auxiliarySchemeNormalizedPoint_coordinate, sub_eq_zero]
    exact (auxiliaryNormalizedEvaluation_third f.appTop.hom).1.trans
      (auxiliaryNormalizedEvaluation_inverse f.appTop.hom).2.symm

/-- An actual auxiliary scheme family gives an actual point of the original normalized slice. -/
def auxiliarySchemeNormalizedSlicePoint : T ⟶ normalizedSlice :=
  normalizedSliceFamilyLift (auxiliarySchemeNormalizedPoint f)
    (auxiliarySchemeNormalizedPoint_satisfies f)

/-- The slice point retains the entire represented normalized auxiliary family. -/
@[reassoc] theorem auxiliarySchemeNormalizedSlicePoint_inclusion :
    auxiliarySchemeNormalizedSlicePoint f ≫ normalizedSliceInclusion =
      auxiliarySchemeNormalizedPoint f := normalizedSliceFamilyLift_inclusion _ _

/-- The slice point retains exactly the normalized coefficient parameter. -/
@[reassoc] theorem auxiliarySchemeNormalizedSlicePoint_base :
    auxiliarySchemeNormalizedSlicePoint f ≫ normalizedSliceInclusion ≫ levelFour.hom =
      T.toSpecΓ ≫ auxiliaryNormalizedCoefficientBase f.appTop.hom := by
  rw [← Category.assoc, auxiliarySchemeNormalizedSlicePoint_inclusion,
    auxiliarySchemeNormalizedPoint_base]

/-- Factoring this normalized family through the original slice is unique. -/
theorem auxiliarySchemeNormalizedSlicePoint_unique (l : T ⟶ normalizedSlice)
    (hl : l ≫ normalizedSliceInclusion = auxiliarySchemeNormalizedPoint f) :
    l = auxiliarySchemeNormalizedSlicePoint f :=
  (cancel_mono normalizedSliceInclusion).mp
    (hl.trans (auxiliarySchemeNormalizedSlicePoint_inclusion f).symm)

end FLT.Mazur.UniversalWeierstrass
