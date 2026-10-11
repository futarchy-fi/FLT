/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SmoothOrderedTranslationTests
public import FLT.Mazur.VariableTranslatedHilbertRepresentation

/-!
# Countably many Hilbert charts with fixed smooth translation bases

The positive power, ordered translation degree, and Hilbert degree index a
fixed family. Every chart-test fiber product is represented by the existing
open intersection and is smooth over the original test.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel FCurve SchemePicard OrderedCurvePower
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {B : X.Modules} (hB : AmpleLineBundle B)

/-- Fixed countable chart indices, including the independent Hilbert degree. -/
abbrev SmoothHilbertTranslationIndex := SmoothTranslationIndex × ℕ

/-- The actual variable Hilbert chart attached to one fixed ordered translation. -/
def smoothHilbertTest (i : SmoothHilbertTranslationIndex) : Over (Spec (.of R)) :=
  variableHilbertTest f i.2 (smoothTranslationTest f i.1)

/-- The original Picard-sheaf section of a point in a fixed smooth chart. -/
def smoothHilbertPoint (i : SmoothHilbertTranslationIndex)
    (T : Over (Spec (.of R))) (a : T ⟶ smoothHilbertTest f i) :
    (relativeFppfSheaf f).obj.obj (op T) :=
  variableHilbertPoint f i.2 hB (smoothTranslationTest f i.1)
    (smoothTranslationClass f hB.2.1 i.1) T a

/-- Fixed chart points restrict along all original test arrows. -/
theorem smoothHilbertPoint_natural (i : SmoothHilbertTranslationIndex)
    {T U : Over (Spec (.of R))} (b : U ⟶ T) (a : T ⟶ smoothHilbertTest f i) :
    smoothHilbertPoint f hB i U (b ≫ a) =
      (relativeFppfSheaf f).obj.map b.op (smoothHilbertPoint f hB i T a) :=
  variableHilbertPoint_natural f i.2 hB _ _ b a

/-- The actual natural map of one fixed chart to the original sheaf. -/
def smoothHilbertMap (i : SmoothHilbertTranslationIndex) :
    uliftYoneda.{1}.obj (smoothHilbertTest f i) ⟶
      (relativeFppfSheaf f).obj ⋙ forget CommGrpCat :=
  variableHilbertPicardMap f i.2 hB (smoothTranslationTest f i.1)
    (smoothTranslationClass f hB.2.1 i.1)

variable (i : SmoothHilbertTranslationIndex) (T : Over (Spec (.of R)))
  (s : (relativeFppfSheaf f).obj.obj (op T))

/-- The actual intersection with the supplied original section. -/
def smoothHilbertOverlap : Over (Spec (.of R)) :=
  variableHilbertOverlap f i.2 (smoothTranslationTest f i.1)
    (smoothTranslationClass f hB.2.1 i.1) T s

/-- The original test projection of the fixed chart intersection. -/
def smoothHilbertOverlapToTest : smoothHilbertOverlap f hB i T s ⟶ T :=
  variableHilbertOverlapToTest f i.2 (smoothTranslationTest f i.1)
    (smoothTranslationClass f hB.2.1 i.1) T s

/-- The original chart projection of the fixed chart intersection. -/
def smoothHilbertOverlapToChart :
    smoothHilbertOverlap f hB i T s ⟶ smoothHilbertTest f i :=
  variableHilbertOverlapToChart f i.2 hB (smoothTranslationTest f i.1)
    (smoothTranslationClass f hB.2.1 i.1) T s

/-- These are the full presheaf pullbacks on every original test. -/
theorem smoothHilbertMap_isPullback :
    IsPullback (uliftYoneda.{1}.map (smoothHilbertOverlapToChart f hB i T s))
      (uliftYoneda.{1}.map (smoothHilbertOverlapToTest f hB i T s))
      (smoothHilbertMap f hB i) (uliftYonedaEquiv.symm s) :=
  variableHilbertPicardMap_isPullback f i.2 hB _ _ T s

instance smoothHilbertOverlapToTest_smooth :
    Smooth (smoothHilbertOverlapToTest f hB i T s).left :=
  variableHilbertOverlapToTest_smooth f i.2 _ _ T s

end FLT.Mazur.HilbertChart
