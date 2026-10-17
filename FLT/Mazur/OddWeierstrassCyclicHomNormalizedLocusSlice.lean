/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassCyclicHomLocusRelabelNormalization
public import FLT.Mazur.OddWeierstrassCyclicHomSliceRelabelNormalization

/-!
# The normalized subgroup locus is closed inside the full odd slice

Forgetting the subgroup equation retains the entire normalized parameter.
The inclusion commutes with the two constructed normalization retractions.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.OddWeierstrassParameter
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n]

/-- Forget only the subgroup equation of the normalized parameter. -/
def cyclicHomNormalizedLocusToSlice :
    cyclicHomNormalizedLocus n ⟶ cyclicHomNormalizedSlice n :=
  cyclicHomNormalizedSliceFamilyLift n
    (cyclicHomNormalizedLocusInclusion n ≫ cyclicHomUniversalMultiplicationLocusInclusion n)
    (by simpa only [Category.id_comp] using
      cyclicHomNormalizedLocus_satisfies n (𝟙 (cyclicHomNormalizedLocus n)))

/-- Forgetting the subgroup equation retains the whole original full parameter. -/
@[reassoc] theorem cyclicHomNormalizedLocusToSlice_inclusion :
    cyclicHomNormalizedLocusToSlice n ≫ cyclicHomNormalizedSliceInclusion n =
      cyclicHomNormalizedLocusInclusion n ≫ cyclicHomUniversalMultiplicationLocusInclusion n :=
  cyclicHomNormalizedSliceFamilyLift_inclusion n _ _

/-- The subgroup condition remains closed inside the actual full normalized slice. -/
instance cyclicHomNormalizedLocusToSlice_isClosedImmersion :
    IsClosedImmersion (cyclicHomNormalizedLocusToSlice n) := by
  have : IsClosedImmersion
      (cyclicHomNormalizedLocusToSlice n ≫ cyclicHomNormalizedSliceInclusion n) := by
    rw [cyclicHomNormalizedLocusToSlice_inclusion]
    infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion
    (cyclicHomNormalizedLocusToSlice n) (cyclicHomNormalizedSliceInclusion n)

/-- Normalization commutes with the actual closed inclusion of the subgroup condition. -/
@[reassoc] theorem cyclicHomLocusNormalization_toSlice :
    cyclicHomLocusNormalization n ≫ cyclicHomNormalizedLocusToSlice n =
      cyclicHomUniversalMultiplicationLocusInclusion n ≫ cyclicHomNormalizationMorphism n := by
  apply (cancel_mono (cyclicHomNormalizedSliceInclusion n)).mp
  simp only [Category.assoc, cyclicHomNormalizedLocusToSlice_inclusion,
    cyclicHomNormalizationMorphism_parameter]
  simpa only [Category.id_comp] using cyclicHomLocusNormalization_parameter n
    (𝟙 (cyclicHomUniversalMultiplicationLocus n))

/-- The normalized subgroup point is the original full normalized slice point. -/
theorem cyclicHomNormalizedLocusPoint_toSlice {T : Scheme}
    (f : T ⟶ (cyclicHomAuxiliaryScheme n).left)
    (h : cyclicHomMultiplicationEquation n f = 0) :
    cyclicHomNormalizedLocusPoint n f h ≫ cyclicHomNormalizedLocusToSlice n =
      cyclicHomNormalizedSlicePoint n f := by
  apply (cancel_mono (cyclicHomNormalizedSliceInclusion n)).mp
  rw [Category.assoc, cyclicHomNormalizedLocusToSlice_inclusion,
    cyclicHomNormalizedLocusPoint_parameter, cyclicHomNormalizedSlicePoint_inclusion]

end FLT.Mazur.OddWeierstrassParameter
