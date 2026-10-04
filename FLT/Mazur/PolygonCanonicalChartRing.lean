/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCubicProjectiveCharts

/-!
# The canonical projective denominator on affine polygon opens

Any actual affine open inside the marked-divisor complement supports the
canonical-denominator chart map. Its target is the coordinate ring of that
open, and its coordinates are the actual section ratios transported through
the open immersion and Gamma-Spec isomorphisms.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.PolygonCubicSections
open FCurve PolygonPinching PolygonPowerNodeEndpoints
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The coordinate of the canonical divisor section in the finite family. -/
def canonicalIndex (n : ℕ) : Fin (n * 3 + 1 + 1) :=
  (cubicCoordinateEquiv.{u} n).symm (.inl ⟨false⟩)

variable (K : Type u) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
  (a : Fin n → Kˣ)

/-- The chosen denominator is the genuine canonical cubic section. -/
lemma finiteCubicFamily_canonicalIndex :
    finiteCubicFamily K n hn p q h a (canonicalIndex.{u} n) =
      divisorSection ((PolygonBoundaryDivisor.cartier K n p hn q h a).1.pow 3) ⊤ := by
  simp only [finiteCubicFamily, canonicalIndex, Equiv.apply_symm_apply, cubicFamily,
    generatingPair]

/-- The marked-divisor complement is contained in the canonical generator open. -/
lemma complement_le_canonical : divisorComplement K n p a ≤
    sectionGeneratorOpen (polygonLine K n hn p q h a 3)
      (finiteCubicFamily K n hn p q h a (canonicalIndex.{u} n)) := by
  have hs : IsIso (sectionHom (polygonLine K n hn p q h a 3)
      (divisorComplement K n p a)
      ((polygonLine K n hn p q h a 3).presheaf.map (homOfLE le_top).op
        (finiteCubicFamily K n hn p q h a (canonicalIndex.{u} n)))) := by
    rw [finiteCubicFamily_canonicalIndex, divisorSection_restrict]
    exact canonicalSection_isIso_complement K n hn p q h a
  exact le_sectionGeneratorOpen _ _ _

variable {R : Type u} [CommRing R] (j : Spec (.of R) ⟶ C.left) [IsOpenImmersion j]
  (hj : Set.range j ⊆ divisorComplement K n p a)

include hj in
/-- Every point of the specified affine image lies in the true denominator open. -/
lemma affine_image_le_canonical : j ''ᵁ ⊤ ≤
    sectionGeneratorOpen (polygonLine K n hn p q h a 3)
      (finiteCubicFamily K n hn p q h a (canonicalIndex.{u} n)) := by
  rw [Scheme.Hom.image_top_eq_opensRange]
  exact le_trans hj (complement_le_canonical K n hn p q h a)

/-- The actual chart ring map in the affine open's coordinate ring. -/
irreducible_def affineCanonicalChartRingMap :
    ProjectiveSpace.chartRing K (Fin (n * 3 + 1 + 1)) (canonicalIndex.{u} n) →+* R :=
  (Scheme.ΓSpecIso (.of R)).hom.hom.comp ((j.appIso ⊤).hom.hom.comp
    (sectionProjectiveChartRingMap (polygonLine K n hn p q h a 3) (n * 3 + 1)
      (finiteCubicFamily K n hn p q h a) (canonicalIndex.{u} n) _
      (affine_image_le_canonical K n hn p q h a j hj) (cubicOpenScalars K _)))

/-- The sealed map retains its defining transport through the actual section rings. -/
lemma affineCanonicalChartRingMap_apply
    (z : ProjectiveSpace.chartRing K (Fin (n * 3 + 1 + 1)) (canonicalIndex.{u} n)) :
    affineCanonicalChartRingMap K n hn p q h a j hj z =
      (Scheme.ΓSpecIso (.of R)).hom ((j.appIso ⊤).hom
        (sectionProjectiveChartRingMap (polygonLine K n hn p q h a 3) (n * 3 + 1)
          (finiteCubicFamily K n hn p q h a) (canonicalIndex.{u} n) _
          (affine_image_le_canonical K n hn p q h a j hj) (cubicOpenScalars K _) z)) := by
  rw [affineCanonicalChartRingMap_def]
  rfl

/-- Projective coordinates evaluate to the actual canonical-denominator section ratios. -/
lemma affineCanonicalChartRingMap_coordinate (k : CubicIndex.{u} n) :
    affineCanonicalChartRingMap K n hn p q h a j hj
      (ProjectiveSpace.coordinate K (Fin (n * 3 + 1 + 1)) (canonicalIndex.{u} n)
        ((cubicCoordinateEquiv n).symm k)) =
      (Scheme.ΓSpecIso (.of R)).hom ((j.appIso ⊤).hom
        (sectionRatioOn (polygonLine K n hn p q h a 3)
          (finiteCubicFamily K n hn p q h a (canonicalIndex.{u} n)) (j ''ᵁ ⊤)
          (affine_image_le_canonical K n hn p q h a j hj)
          (cubicFamily K n hn p q h a k))) := by
  rw [affineCanonicalChartRingMap_apply, sectionProjectiveChartRingMap_coordinate]
  simp only [finiteCubicFamily, Equiv.apply_symm_apply]

/-- The coefficient map is the pullback along the actual structural morphism. -/
lemma affineCanonicalChartRingMap_scalar (c : K) :
    affineCanonicalChartRingMap K n hn p q h a j hj
      (ProjectiveSpace.chartScalars K (Fin (n * 3 + 1 + 1)) (canonicalIndex.{u} n) c) =
      (Scheme.ΓSpecIso (.of R)).hom
        ((j ≫ C.hom).appTop ((Scheme.ΓSpecIso (.of K)).inv c)) := by
  rw [affineCanonicalChartRingMap_apply, sectionProjectiveChartRingMap_scalar]
  congr 1
  change (j.appIso ⊤).hom (C.left.presheaf.map (homOfLE le_top).op
    (C.hom.appTop ((Scheme.ΓSpecIso (.of K)).inv c))) = _
  rw [Scheme.Hom.appIso_hom', ← CommRingCat.comp_apply, Scheme.Hom.map_appLE,
    Scheme.Hom.comp_appTop]
  rfl

end FLT.Mazur.PolygonCubicSections
