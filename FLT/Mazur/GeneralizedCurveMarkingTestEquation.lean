/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineWeierstrassBaseChange
public import FLT.Mazur.GeneralizedCurveMarkingLocalTestMorphism

/-!
# Concrete cubic equations on non-Noetherian affine tests

The five original affine-frame coefficients extend along the actual test
map. Their integral cubic presents the whole pulled-back glued cubic, with
the original whole-family morphism and infinity section retained exactly.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.GeneralizedEllipticCurve
open GroupSectionBaseChange WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T : Scheme} [IsLocallyNoetherian S] [IsAffine T]
  (E : GeneralizedEllipticCurve S) (s : 𝟙_ (Over S) ⟶ E.group)
  (i : SmoothMarkingAffineChart E s) (h : T ⟶ i.base.1.toScheme)

/-- The actual coefficient equation over the unrestricted affine test ring. -/
def smoothMarkingTestEquation : WeierstrassCurve Γ(T, ⊤) :=
  (smoothMarkingAffineEquation E s i).map h.appTop.hom

/-- Extending the original coefficients presents the whole cubic on this affine test. -/
def smoothMarkingTestPresentation : integralCurve (smoothMarkingTestEquation E s i h) ≅
    smoothMarkingPulledCubic E s (h ≫ i.base.1.ι) :=
  affineIntegralBaseChangeIso (smoothMarkingAffineEquation E s i) h ≪≫
    smoothMarkingLocalTestIso E s i h

/-- The presentation retains the actual original coefficient projection. -/
@[reassoc] theorem smoothMarkingTestPresentation_projection :
    (smoothMarkingTestPresentation E s i h).hom ≫
      smoothMarkingPulledProjection E s (h ≫ i.base.1.ι) =
        affineIntegralCoefficient (smoothMarkingAffineEquation E s i) h ≫
          smoothMarkingGluedChart E s i := by
  change ((affineIntegralBaseChangeIso (smoothMarkingAffineEquation E s i) h).hom ≫
    (smoothMarkingLocalTestIso E s i h).hom) ≫ _ = _
  rw [Category.assoc, smoothMarkingLocalTestIso_projection, ← Category.assoc]
  exact congrArg (· ≫ smoothMarkingGluedChart E s i)
    (affineIntegralBaseChangeIso_fst (smoothMarkingAffineEquation E s i) h)

/-- The presentation retains the actual test structure map. -/
@[reassoc] theorem smoothMarkingTestPresentation_over :
    (smoothMarkingTestPresentation E s i h).hom ≫
      smoothMarkingPulledBase E s (h ≫ i.base.1.ι) =
        affineIntegralStructure (smoothMarkingTestEquation E s i h) := by
  change ((affineIntegralBaseChangeIso (smoothMarkingAffineEquation E s i) h).hom ≫
    (smoothMarkingLocalTestIso E s i h).hom) ≫ _ = _
  rw [Category.assoc, smoothMarkingLocalTestIso_over]
  exact affineIntegralBaseChangeIso_snd (smoothMarkingAffineEquation E s i) h

/-- The coefficient presentation retains the original infinity section on the entire test. -/
@[reassoc] theorem smoothMarkingTestPresentation_zero :
    affineIntegralZero (U := T) (smoothMarkingTestEquation E s i h) ≫
      (smoothMarkingTestPresentation E s i h).hom =
        smoothMarkingPulledZero E s (h ≫ i.base.1.ι) := by
  apply Limits.pullback.hom_ext
  · change _ ≫ smoothMarkingPulledProjection E s (h ≫ i.base.1.ι) =
      smoothMarkingPulledZero E s (h ≫ i.base.1.ι) ≫
        smoothMarkingPulledProjection E s (h ≫ i.base.1.ι)
    rw [Category.assoc, smoothMarkingTestPresentation_projection,
      ← Category.assoc]
    change (affineIntegralZero ((smoothMarkingAffineEquation E s i).map h.appTop.hom) ≫
      affineIntegralCoefficient (smoothMarkingAffineEquation E s i) h) ≫ _ = _
    rw [affineIntegralCoefficient_zero, Category.assoc, smoothMarkingPulledZero_projection]
    change h ≫ smoothMarkingAffineZero E s i ≫ smoothMarkingGluedChart E s i = _
    rw [smoothMarkingAffineZero_chart, Category.assoc]
  · change _ ≫ smoothMarkingPulledBase E s (h ≫ i.base.1.ι) =
      smoothMarkingPulledZero E s (h ≫ i.base.1.ι) ≫
        smoothMarkingPulledBase E s (h ≫ i.base.1.ι)
    rw [Category.assoc, smoothMarkingTestPresentation_over,
      affineIntegralZero_over, smoothMarkingPulledZero_over]

/-- The original whole test family maps to the actual coefficient equation. -/
def smoothMarkingToTestEquation : (E.baseChange (h ≫ i.base.1.ι)).curve.left ⟶
    integralCurve (smoothMarkingTestEquation E s i h) :=
  smoothMarkingToPulledCubic E s (h ≫ i.base.1.ι) ≫
    (smoothMarkingTestPresentation E s i h).inv

/-- The explicit coefficient map recovers the original whole-family map. -/
@[reassoc] theorem smoothMarkingToTestEquation_presentation :
    smoothMarkingToTestEquation E s i h ≫ (smoothMarkingTestPresentation E s i h).hom =
      smoothMarkingToPulledCubic E s (h ≫ i.base.1.ι) := by
  rw [smoothMarkingToTestEquation, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The original pulled marking maps to the actual infinity of the coefficient equation. -/
@[reassoc] theorem smoothMarkingToTestEquation_marking :
    (pullSection (h ≫ i.base.1.ι) s ≫ (E.baseChange (h ≫ i.base.1.ι)).inclusion).left ≫
      smoothMarkingToTestEquation E s i h =
        affineIntegralZero (U := T) (smoothMarkingTestEquation E s i h) := by
  apply (cancel_mono (smoothMarkingTestPresentation E s i h).hom).mp
  rw [Category.assoc, smoothMarkingToTestEquation_presentation,
    smoothMarkingToPulledCubic_marking, smoothMarkingTestPresentation_zero (T := T) E s i h]

/-- The original whole-family morphism to the concrete equation is proper on every test. -/
instance smoothMarkingToTestEquation_isProper : IsProper (smoothMarkingToTestEquation E s i h) := by
  unfold smoothMarkingToTestEquation
  infer_instance

end FLT.Mazur.GeneralizedEllipticCurve
