/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FaithfulNeighborhoodCurve
public import FLT.Mazur.RelativePicardFppfBaseChange

/-!
# Comparing retained Hilbert tests with the localized proper curve

The original affine test and its local-base version have the same source.
Their explicit comparison over the original base retains the translation
coordinate. The curves over these tests are canonically isomorphic.
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
local notation "D" => fun x ↦ data f hL T s x
local notation "E" => fun x ↦ Sigma.fst (Sigma.snd (chartData f hL T s x))
local notation "b" => fun x ↦ spectrumBase
  (Over.hom (Sigma.fst (Sigma.snd (chartData f hL T s x))))
    (Sigma.fst (data f hL T s x))

/-- Forgetting the localized base recovers exactly the original affine test. -/
def originalTestIso (x : T.left) :
    (Over.map (b x)).obj (localTest f hL T s x) ≅ test f hL T s x :=
  Over.isoMk (Iso.refl _) (by simpa using (localTest_original_base f hL T s x).symm)

@[simp]
theorem originalTestIso_hom_left (x : T.left) :
    (originalTestIso f hL T s x).hom.left = 𝟙 _ := rfl

@[simp]
theorem originalTestIso_inv_left (x : T.left) :
    (originalTestIso f hL T s x).inv.left = 𝟙 _ := rfl

/-- The original translation is restricted by the actual principal-open inclusion. -/
def translationToOriginal (x : T.left) :
    (Over.map (b x)).obj (localTranslation f hL T s x) ⟶ E x :=
  Over.homMk (sourceOpen (E x).hom (D x).1).ι
    (spectrumMap_base (E x).hom (D x).1).symm

/-- The local independent coordinate recovers the original overlap coordinate. -/
@[reassoc]
theorem coordinate_base_comparison (x : T.left) :
    (Over.map (b x)).map (localCoordinate f hL T s x) ≫ translationToOriginal f hL T s x =
      (originalTestIso f hL T s x).hom ≫ toIntersection f hL T s x ≫
        coordinate f hL T s x := by
  apply Over.OverMorphism.ext
  simpa only [Over.comp_left, Over.map_map_left, translationToOriginal, Over.homMk_left,
    originalTestIso_hom_left, Category.id_comp] using
    localCoordinate_original f hL T s x

/-- The actual curve over the retained test agrees with the localized curve over that test. -/
def testCurveIso (x : T.left) :
    Limits.pullback (FaithfulNeighborhoodCurve.map f (E x).hom (D x).1)
        (localTest f hL T s x).hom ≅
      Limits.pullback f (test f hL T s x).hom :=
  relativeBaseChangeTotalIso f (b x) (localTest f hL T s x) ≪≫
    { hom := relativeTotalMap f (originalTestIso f hL T s x).hom
      inv := relativeTotalMap f (originalTestIso f hL T s x).inv
      hom_inv_id := by rw [← relativeTotalMap_comp, Iso.hom_inv_id, relativeTotalMap_id]
      inv_hom_id := by rw [← relativeTotalMap_comp, Iso.inv_hom_id, relativeTotalMap_id] }

/-- The curve comparison keeps the original affine test projection. -/
@[reassoc]
theorem testCurveIso_hom_snd (x : T.left) :
    (testCurveIso f hL T s x).hom ≫ Limits.pullback.snd f (test f hL T s x).hom =
      Limits.pullback.snd _ _ := by
  simp [testCurveIso]

end FLT.Mazur.OrderedHilbertFaithfulTestCover
