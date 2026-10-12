/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OrderedHilbertFaithfulTestCover

/-!
# Original Picard classes on the faithful-base affine test cover

The constructed covering arrows preserve the original sheaf section and the
original Hilbert parameter. Their independent translation coordinates map to
the constructed affine, faithfully flat translation bases over local spectra.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
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
local notation "I" => fun x ↦ intersection f hL T s x

/-- Each actual affine cover member as a test over the original coefficient ring. -/
def test (x : T.left) : Over (Spec (.of R)) :=
  Over.mk ((D x).2.2.1 ≫ (I x).hom)

/-- The original full-intersection inclusion, retaining the original structural map. -/
def toIntersection (x : T.left) : test f hL T s x ⟶ I x := Over.homMk (D x).2.2.1

/-- The actual covering arrow in the original relative site. -/
def testArrow (x : T.left) : test f hL T s x ⟶ T :=
  toIntersection f hL T s x ≫ toTest f hL T s x

/-- These very arrows generate a covering sieve in the original fppf site. -/
theorem covering : Sieve.ofArrows (test f hL T s) (testArrow f hL T s) ∈
    (Scheme.fppfTopology.over (Spec (.of R))) T := by
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
  exact Precoverage.generate_mem_toGrothendieck (fppfCover f hL T s).mem₀

/-- The original full Hilbert parameter of a constructed affine cover member. -/
def toOriginalChart (x : T.left) : test f hL T s x ⟶
    variableHilbertTest f (chartData f hL T s x).1.2 (E x) :=
  toIntersection f hL T s x ≫ variableHilbertOverlapToChart f
    (chartData f hL T s x).1.2 hL (E x) (chartClass f hL T s x) T s

/-- The ORIGINAL Picard section is preserved on each constructed affine cover member. -/
theorem original_class (x : T.left) :
    variableHilbertPoint f (chartData f hL T s x).1.2 hL (E x) (chartClass f hL T s x)
      (test f hL T s x) (toOriginalChart f hL T s x) =
        (relativeFppfSheaf f).obj.map (testArrow f hL T s x).op s := by
  have h := congrArg ((relativeFppfSheaf f).obj.map (toIntersection f hL T s x).op)
    (variableHilbertOverlap_class f (chartData f hL T s x).1.2 hL
      (E x) (chartClass f hL T s x) T s)
  simpa only [toOriginalChart, variableHilbertPoint_natural, testArrow, intersection, toTest,
    op_comp, Functor.map_comp, ConcreteCategory.comp_apply] using h

/-- The constructed translation base over its actual localized coefficient spectrum. -/
def localTranslation (x : T.left) : Over (Spec (.of (BaseRing (E x).hom (D x).1))) :=
  Over.mk (spectrumMap (E x).hom (D x).1)

instance localTranslation_affine (x : T.left) :
    IsAffine (localTranslation f hL T s x).left := source_affine (E x).hom (D x).1

instance localTranslation_etale (x : T.left) :
    Etale (localTranslation f hL T s x).hom := spectrumMap_etale (E x).hom (D x).1

instance localTranslation_surjective (x : T.left) :
    Surjective (localTranslation f hL T s x).hom := spectrumMap_surjective (E x).hom (D x).1

/-- The original affine parameter source over the same localized coefficient spectrum. -/
def localTest (x : T.left) : Over (Spec (.of (BaseRing (E x).hom (D x).1))) :=
  Over.mk ((D x).2.2.2.1 ≫ spectrumMap (E x).hom (D x).1)

instance localTest_affine (x : T.left) : IsAffine (localTest f hL T s x).left :=
  data_affine f hL T s x

/-- The retained independent translation coordinate over the localized base. -/
def localCoordinate (x : T.left) :
    localTest f hL T s x ⟶ localTranslation f hL T s x := Over.homMk (D x).2.2.2.1

/-- Replacing the base spectrum retains the ORIGINAL test structural map. -/
@[reassoc]
theorem localTest_original_base (x : T.left) :
    (localTest f hL T s x).hom ≫ spectrumBase (E x).hom (D x).1 =
      (test f hL T s x).hom := (data_spec f hL T s x).2.2.2.2

/-- The independent translation coordinate is the original full-intersection coordinate. -/
@[reassoc]
theorem localCoordinate_original (x : T.left) :
    (localCoordinate f hL T s x).left ≫ (sourceOpen (E x).hom (D x).1).ι =
      (toIntersection f hL T s x).left ≫ (coordinate f hL T s x).left :=
  (data_spec f hL T s x).2.2.2.1

end FLT.Mazur.OrderedHilbertFaithfulTestCover
