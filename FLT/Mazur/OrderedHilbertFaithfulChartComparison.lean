/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OrderedHilbertFaithfulParameter
public import FLT.Mazur.VariableHilbertFixedBasePicard

/-!
# The original translated chart on the localized proper curve

Both its independent translation coordinate and its full Hilbert parameter
are retained. Their translated Picard class is the actual original section.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.OrderedHilbertFaithfulTestCover
open HilbertChart CartierAbel SchemePicard FCurve AffineEtaleFaithfulNeighborhood
open OrderedHilbertAffineEtaleTestCover
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (T : Over (Spec (.of R))) (s : (relativeFppfSheaf f).obj.obj (op T))
local notation "E" => fun x ↦ Sigma.fst (Sigma.snd (chartData f hL T s x))
local notation "b" => fun x ↦ spectrumBase
  (Over.hom (Sigma.fst (Sigma.snd (chartData f hL T s x))))
    (Sigma.fst (data f hL T s x))
local notation "q" => fun x ↦ FaithfulNeighborhoodCurve.map f
  (Over.hom (Sigma.fst (Sigma.snd (chartData f hL T s x))))
    (Sigma.fst (data f hL T s x))
local notation "degree" => fun x ↦ Prod.snd (Sigma.fst (chartData f hL T s x))

/-- The original varying translation section on the constructed faithful base. -/
def localTranslationClass (x : T.left) :
    (relativeFppfSheaf (q x)).obj.obj (op (localTranslation f hL T s x)) :=
  fixedBaseTranslationClass f (b x) (E x) (localTranslation f hL T s x)
    (translationToOriginal f hL T s x) (chartClass f hL T s x)

/-- The actual localized varying chart point, with both original coordinates. -/
def localChartParameter (x : T.left) :
    localTest f hL T s x ⟶
      variableHilbertTest (q x) (degree x) (localTranslation f hL T s x) :=
  variableHilbertLift (q x) (degree x) (localTranslation f hL T s x)
    (localCoordinate f hL T s x) (localHilbertParameter f hL T s x)

/-- The local chart still has the original independent translation coordinate. -/
theorem localChartParameter_base (x : T.left) :
    localChartParameter f hL T s x ≫
        variableHilbertBase (q x) (degree x) (localTranslation f hL T s x) =
      localCoordinate f hL T s x := prod.lift_fst _ _

/-- The local chart still has the full original Hilbert family. -/
theorem localChartParameter_hilbert (x : T.left) :
    localChartParameter f hL T s x ≫
        variableHilbertParameter (q x) (degree x) (localTranslation f hL T s x) =
      localHilbertParameter f hL T s x := prod.lift_snd _ _

/-- The localized translated chart map is precisely the transported original chart map. -/
theorem localChartParameter_picard (x : T.left) :
    variableHilbertPoint (q x) (degree x) (fixedBaseAmple f (b x) hL)
        (localTranslation f hL T s x) (localTranslationClass f hL T s x)
        (localTest f hL T s x) (localChartParameter f hL T s x) =
      (localPicardIso f hL T s x).hom
        (variableHilbertPoint f (degree x) hL (E x) (chartClass f hL T s x)
          (test f hL T s x) (toOriginalChart f hL T s x)) := by
  have hb : (Over.map (b x)).map (localCoordinate f hL T s x) ≫
      translationToOriginal f hL T s x =
        ((originalTestIso f hL T s x).hom ≫ toOriginalChart f hL T s x) ≫
          variableHilbertBase f (degree x) (E x) := by
    simpa only [toOriginalChart, coordinate, faithfulOverlapCoordinate, Category.assoc] using
      coordinate_base_comparison f hL T s x
  have h := variableHilbertFixedBase_picard f (b x) hL (degree x) (E x)
    (localTranslation f hL T s x) (translationToOriginal f hL T s x)
    (chartClass f hL T s x) (localTest f hL T s x)
    ((originalTestIso f hL T s x).hom ≫ toOriginalChart f hL T s x)
    (localCoordinate f hL T s x) hb
  change _ = (relativeFppfBaseChange f (b x)).hom.hom.app (op (localTest f hL T s x))
    ((relativeFppfSheaf f).obj.map (originalTestIso f hL T s x).hom.op
      (variableHilbertPoint f (degree x) hL (E x) (chartClass f hL T s x)
        (test f hL T s x) (toOriginalChart f hL T s x)))
  simpa only [localChartParameter, localTranslationClass, localHilbertParameter,
    originalHilbertParameter, Category.assoc, variableHilbertPoint_natural] using h

/-- The actual localized chart represents the original section on the retained affine test. -/
theorem localChartParameter_section (x : T.left) :
    variableHilbertPoint (q x) (degree x) (fixedBaseAmple f (b x) hL)
        (localTranslation f hL T s x) (localTranslationClass f hL T s x)
        (localTest f hL T s x) (localChartParameter f hL T s x) =
      localSection f hL T s x := by
  rw [localChartParameter_picard, localSection_original_chart]

end FLT.Mazur.OrderedHilbertFaithfulTestCover
