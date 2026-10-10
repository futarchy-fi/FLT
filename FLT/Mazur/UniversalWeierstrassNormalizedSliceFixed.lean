/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassNormalizedSliceRing
public import FLT.Mazur.UniversalWeierstrassAuxiliaryNormalEquation

/-!
# Canonical normalization fixes the constructed slice

The four equations force the frame translations and shear to vanish and the
two unit differences to agree. Hence the constructed normalization is identity.
-/

@[expose] public noncomputable section

open WeierstrassCurve

namespace FLT.Mazur.UniversalWeierstrass

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {R : Type} [CommRing R] (g : AuxiliarySectionRing →+* R)

/-- The four quotient relations have exactly the intended original coordinate meaning. -/
theorem satisfiesNormalization_coordinates (h : SatisfiesNormalization g) :
    g (auxiliaryCoordinate frameLabelFirst frameLabelFirst_ne 0) = 0 ∧
    g (auxiliaryCoordinate frameLabelFirst frameLabelFirst_ne 1) = 0 ∧
    g (auxiliaryCoordinate frameLabelThird frameLabelThird_ne 1) = 0 ∧
    g (auxiliaryCoordinate frameLabelThird frameLabelThird_ne 0) =
      g (auxiliaryCoordinate frameLabelFirst⁻¹ (inv_ne_one.mpr frameLabelFirst_ne) 1) := by
  refine ⟨h 0, h 1, h 2, ?_⟩
  have he := h 3
  change g (_ - _) = 0 at he
  exact sub_eq_zero.mp ((map_sub g _ _).symm.trans he)

/-- Horizontal and vertical unit differences coincide on the actual normalized slice. -/
theorem normalizedSlice_frameUnits (h : SatisfiesNormalization g) :
    Units.map (g : AuxiliarySectionRing →* R) auxiliaryFrameHorizontalUnit =
      Units.map (g : AuxiliarySectionRing →* R) auxiliaryFrameVerticalUnit := by
  obtain ⟨hx, hy, _, he⟩ := satisfiesNormalization_coordinates g h
  apply Units.ext
  change g (auxiliaryFrameHorizontalUnit : AuxiliarySectionRing) =
    g (auxiliaryFrameVerticalUnit : AuxiliarySectionRing)
  rw [auxiliaryFrameHorizontalUnit_val, auxiliaryFrameVerticalUnit_val, map_sub, map_sub,
    hx, hy, he]

/-- Canonical normalization is the identity admissible change on the constructed slice. -/
theorem normalizedSlice_frameChange (h : SatisfiesNormalization g) :
    auxiliaryFrameChange g = 1 := by
  obtain ⟨hx, hy, hw, _⟩ := satisfiesNormalization_coordinates g h
  rw [auxiliaryFrameChange, hx, hy, hw, normalizedSlice_frameUnits g h]
  simp only [WeierstrassFrameNormalization.change, WeierstrassFrameNormalization.scale,
    mul_inv_cancel, sub_self, zero_mul, VariableChange.one_def]

/-- The original pulled-back equation on the slice already is its canonical normalized equation. -/
theorem normalizedSlice_equation_fixed (h : SatisfiesNormalization g) :
    auxiliaryNormalizedEquation g = auxiliaryPullbackEquation g := by
  rw [auxiliaryNormalizedEquation, normalizedSlice_frameChange g h, one_smul]

/-- The slice equation has the explicit normal form, with its original full marking retained. -/
theorem normalizedSlice_equation_form (h : SatisfiesNormalization g) :
    auxiliaryPullbackEquation g = WeierstrassFrameNormalEquation.equation
      (auxiliaryPullbackEquation g).a₁ (auxiliaryPullbackEquation g).a₂
      (auxiliaryFrameSeparation g) := by
  simpa only [normalizedSlice_equation_fixed g h] using auxiliaryNormalizedEquation_eq g

end FLT.Mazur.UniversalWeierstrass
