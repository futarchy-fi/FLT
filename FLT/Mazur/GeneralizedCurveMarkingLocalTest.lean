/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveMarkingPulledCartesian

/-!
# Actual affine cubic charts on unrestricted local tests

Pulling an original affine cubic chart to any scheme recovers the pullback
of the global cubic. The actual affine infinity section and its ideal are
also recovered from the global infinity section.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.GeneralizedEllipticCurve
open WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T : Scheme} [IsLocallyNoetherian S] (E : GeneralizedEllipticCurve S)
  (s : 𝟙_ (Over S) ⟶ E.group) (i : SmoothMarkingAffineChart E s)

/-- The actual integral infinity section over its original affine base open. -/
def smoothMarkingAffineZero : i.base.1.toScheme ⟶ (smoothMarkingAffineDiagram E s).obj i :=
  i.base.1.toScheme.toSpecΓ ≫ integralCurveZero (smoothMarkingAffineEquation E s i)

/-- The original affine infinity is a section of the affine cubic structure map. -/
@[reassoc] theorem smoothMarkingAffineZero_over :
    smoothMarkingAffineZero E s i ≫ smoothMarkingAffineStructure E s i = 𝟙 _ := by
  rw [smoothMarkingAffineZero, smoothMarkingAffineStructure,
    Category.assoc, ← Category.assoc (integralCurveZero _), integralCurveZero_structure,
    Category.id_comp]
  exact i.base.1.toScheme.isoSpec.hom_inv_id

/-- The affine infinity is the actual restriction of the global infinity section. -/
@[reassoc] theorem smoothMarkingAffineZero_chart :
    smoothMarkingAffineZero E s i ≫ smoothMarkingGluedChart E s i =
      i.base.1.ι ≫ smoothMarkingGluedZero E s := by
  rw [smoothMarkingAffineZero, Category.assoc, smoothMarkingGluedZero_chart]

/-- The actual infinity sections form a categorical pullback square. -/
theorem smoothMarkingAffineZero_isPullback :
    IsPullback (smoothMarkingAffineZero E s i) i.base.1.ι
      (smoothMarkingGluedChart E s i) (smoothMarkingGluedZero E s) :=
  FCurve.section_isPullback_of_cartesian (smoothMarkingGluedChart_isPullback E s i).flip
    (smoothMarkingAffineZero E s i) (smoothMarkingGluedZero E s)
    (smoothMarkingAffineZero_over E s i) (smoothMarkingGluedZero_over E s)
    (smoothMarkingAffineZero_chart E s i)

/-- The affine chart retains the full global infinity ideal. -/
theorem smoothMarkingAffineZero_ker :
    (smoothMarkingGluedZero E s).ker.comap (smoothMarkingGluedChart E s i) =
      (smoothMarkingAffineZero E s i).ker :=
  FCurve.section_ker_comap_of_cartesian (smoothMarkingGluedChart_isPullback E s i).flip
    (smoothMarkingAffineZero E s i) (smoothMarkingGluedZero E s)
    (smoothMarkingAffineZero_over E s i) (smoothMarkingGluedZero_over E s)
    (smoothMarkingAffineZero_chart E s i)

variable (h : T ⟶ i.base.1.toScheme)

/-- Every test of an original affine chart has the actual global cubic pullback square. -/
theorem smoothMarkingLocalTest_isPullback :
    IsPullback
      (Limits.pullback.fst (smoothMarkingAffineStructure E s i) h ≫
        smoothMarkingGluedChart E s i)
      (Limits.pullback.snd (smoothMarkingAffineStructure E s i) h)
      (smoothMarkingGluedBase E s) (h ≫ i.base.1.ι) :=
  (IsPullback.of_hasPullback (smoothMarkingAffineStructure E s i) h).paste_horiz
    (smoothMarkingGluedChart_isPullback E s i).flip

/-- The pulled original affine cubic is the actual global cubic on this unrestricted test. -/
def smoothMarkingLocalTestIso :
    Limits.pullback (smoothMarkingAffineStructure E s i) h ≅
      smoothMarkingPulledCubic E s (h ≫ i.base.1.ι) :=
  (smoothMarkingLocalTest_isPullback E s i h).isoPullback

/-- The local-test comparison retains the original cubic chart projection. -/
@[reassoc] theorem smoothMarkingLocalTestIso_projection :
    (smoothMarkingLocalTestIso E s i h).hom ≫
      smoothMarkingPulledProjection E s (h ≫ i.base.1.ι) =
        Limits.pullback.fst (smoothMarkingAffineStructure E s i) h ≫
          smoothMarkingGluedChart E s i := IsPullback.isoPullback_hom_fst _

/-- The local-test comparison retains the actual test base. -/
@[reassoc] theorem smoothMarkingLocalTestIso_over :
    (smoothMarkingLocalTestIso E s i h).hom ≫
      smoothMarkingPulledBase E s (h ≫ i.base.1.ι) =
        Limits.pullback.snd (smoothMarkingAffineStructure E s i) h :=
  IsPullback.isoPullback_hom_snd _

end FLT.Mazur.GeneralizedEllipticCurve
