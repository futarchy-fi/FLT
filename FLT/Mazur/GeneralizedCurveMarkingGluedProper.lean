/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveMarkingGluedMorphism
public import FLT.Mazur.GeneralizedCurveMarkingGluedRecovery
public import FLT.Mazur.WeierstrassIntegralProper

/-!
# Properness of the glued cubic and the original whole-family map

Cartesian chart recovery descends properness of the actual integral cubics
to the global structure map. The entire original family then maps properly
to this scheme, including higher polygons and nonreduced bases.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} [IsLocallyNoetherian S] (E : GeneralizedEllipticCurve S)
  (s : 𝟙_ (Over S) ⟶ E.group)

/-- Each constructed affine cubic is proper over its original affine chart base. -/
instance smoothMarkingAffineStructure_isProper (i : SmoothMarkingAffineChart E s) :
    IsProper (smoothMarkingAffineStructure E s i) := by
  unfold smoothMarkingAffineStructure
  infer_instance

/-- The actual glued cubic is proper over the original locally Noetherian base. -/
instance smoothMarkingGluedBase_isProper : IsProper (smoothMarkingGluedBase E s) := by
  apply IsZariskiLocalAtTarget.of_openCover (smoothMarkingFrameCover E s)
  intro i
  change IsProper (Limits.pullback.snd (smoothMarkingGluedBase E s) i.base.1.ι)
  rw [← MorphismProperty.cancel_left_of_respectsIso @IsProper
    (smoothMarkingGluedChart_isPullback E s i).flip.isoPullback.hom,
    IsPullback.isoPullback_hom_snd]
  infer_instance

/-- The whole original curve maps properly to the actually glued cubic, even for polygons. -/
theorem smoothMarkingToGluedCubic_isProper : IsProper (smoothMarkingToGluedCubic E s) := by
  let _ : IsProper E.curve.hom := E.family.family.1
  have : IsProper (smoothMarkingToGluedCubic E s ≫ smoothMarkingGluedBase E s) := by
    rw [smoothMarkingToGluedCubic_over]
    infer_instance
  exact IsProper.of_comp (smoothMarkingToGluedCubic E s) (smoothMarkingGluedBase E s)

end FLT.Mazur.GeneralizedEllipticCurve
