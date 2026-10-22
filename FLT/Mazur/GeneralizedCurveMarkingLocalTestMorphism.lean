/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveMarkingGluedCartesian
public import FLT.Mazur.GeneralizedCurveMarkingLocalTest

/-!
# Original whole-curve maps on arbitrary local tests

The original affine-frame whole-curve morphism pulls back to every test.
The actual family associator and the local cubic comparison identify this
map with the pullback of the glued whole-family morphism, preserving infinity.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T : Scheme} [IsLocallyNoetherian S] (E : GeneralizedEllipticCurve S)
  (s : 𝟙_ (Over S) ⟶ E.group) (i : SmoothMarkingAffineChart E s)
  (h : T ⟶ i.base.1.toScheme)

/-- The actual local whole-curve map after an arbitrary change of its original affine base. -/
def smoothMarkingLocalTestMorphism : ((E.baseChange i.base.1.ι).baseChange h).curve.left ⟶
    Limits.pullback (smoothMarkingAffineStructure E s i) h :=
  Limits.pullback.lift
    (Limits.pullback.fst (E.baseChange i.base.1.ι).curve.hom h ≫
      smoothMarkingAffineMorphism E s i)
    (Limits.pullback.snd (E.baseChange i.base.1.ι).curve.hom h)
    (by rw [Category.assoc, smoothMarkingAffineMorphism_over];
        exact Limits.pullback.condition)

/-- Projection recovers the actual affine-frame whole-curve map. -/
@[reassoc] theorem smoothMarkingLocalTestMorphism_fst :
    smoothMarkingLocalTestMorphism E s i h ≫ Limits.pullback.fst _ _ =
      Limits.pullback.fst (E.baseChange i.base.1.ι).curve.hom h ≫
        smoothMarkingAffineMorphism E s i := Limits.pullback.lift_fst _ _ _

/-- The test morphism retains the iterated original family's structure map. -/
@[reassoc] theorem smoothMarkingLocalTestMorphism_snd :
    smoothMarkingLocalTestMorphism E s i h ≫ Limits.pullback.snd _ _ =
      ((E.baseChange i.base.1.ι).baseChange h).curve.hom :=
  Limits.pullback.lift_snd _ _ _

/-- The actual family associator identifies the local test map with the global test map. -/
theorem smoothMarkingLocalTestMorphism_global :
    (E.baseChangeCompIso i.base.1.ι h).hom.curve.left ≫
      smoothMarkingLocalTestMorphism E s i h ≫ (smoothMarkingLocalTestIso E s i h).hom =
        smoothMarkingToPulledCubic E s (h ≫ i.base.1.ι) := by
  apply Limits.pullback.hom_ext
  · change _ ≫ smoothMarkingPulledProjection E s (h ≫ i.base.1.ι) =
      smoothMarkingToPulledCubic E s (h ≫ i.base.1.ι) ≫
        smoothMarkingPulledProjection E s (h ≫ i.base.1.ι)
    simp only [Category.assoc, smoothMarkingLocalTestIso_projection,
      smoothMarkingLocalTestMorphism_fst_assoc, smoothMarkingAffineMorphism_chart,
      baseChangeCompIso_fst_fst_assoc, smoothMarkingToPulledCubic_projection]
  · change _ ≫ smoothMarkingPulledBase E s (h ≫ i.base.1.ι) =
      smoothMarkingToPulledCubic E s (h ≫ i.base.1.ι) ≫
        smoothMarkingPulledBase E s (h ≫ i.base.1.ι)
    rw [Category.assoc, Category.assoc, smoothMarkingLocalTestIso_over,
      smoothMarkingLocalTestMorphism_snd, smoothMarkingToPulledCubic_over]
    exact (E.baseChangeCompIso i.base.1.ι h).hom.curve.w

/-- The local-test infinity section is constructed from the actual affine infinity. -/
def smoothMarkingLocalTestZero : T ⟶ Limits.pullback (smoothMarkingAffineStructure E s i) h :=
  Limits.pullback.lift (h ≫ smoothMarkingAffineZero E s i) (𝟙 T)
    (by rw [Category.assoc, smoothMarkingAffineZero_over,
      Category.comp_id, Category.id_comp])

/-- The local cubic comparison retains infinity on the whole unrestricted test. -/
@[reassoc] theorem smoothMarkingLocalTestZero_global :
    smoothMarkingLocalTestZero E s i h ≫ (smoothMarkingLocalTestIso E s i h).hom =
      smoothMarkingPulledZero E s (h ≫ i.base.1.ι) := by
  apply Limits.pullback.hom_ext
  · change _ ≫ smoothMarkingPulledProjection E s (h ≫ i.base.1.ι) =
      smoothMarkingPulledZero E s (h ≫ i.base.1.ι) ≫
        smoothMarkingPulledProjection E s (h ≫ i.base.1.ι)
    rw [Category.assoc, smoothMarkingLocalTestIso_projection,
      ← Category.assoc, smoothMarkingLocalTestZero, Limits.pullback.lift_fst,
      Category.assoc, smoothMarkingAffineZero_chart, smoothMarkingPulledZero_projection,
      Category.assoc]
  · change _ ≫ smoothMarkingPulledBase E s (h ≫ i.base.1.ι) =
      smoothMarkingPulledZero E s (h ≫ i.base.1.ι) ≫
        smoothMarkingPulledBase E s (h ≫ i.base.1.ι)
    rw [Category.assoc, smoothMarkingLocalTestIso_over, smoothMarkingLocalTestZero,
      Limits.pullback.lift_snd, smoothMarkingPulledZero_over]

end FLT.Mazur.GeneralizedEllipticCurve
