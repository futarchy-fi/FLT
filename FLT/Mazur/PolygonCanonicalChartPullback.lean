/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCanonicalChartRing
public import FLT.Mazur.PolygonCubicProjectiveMorphism
public import FLT.Mazur.ModuleSectionProjectiveTransition

/-!
# The canonical chart ring map is the global cubic pullback

The sealed map to an affine coordinate ring is obtained from the actual
structure-sheaf pullback along the previously constructed global morphism.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.PolygonCubicSections
open FCurve PolygonPinching PolygonPowerNodeEndpoints ProjectiveSpace
attribute [local instance] MvPolynomial.gradedAlgebra
variable (K : Type) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
  (a : Fin n → Kˣ) {R : Type} [CommRing R]
  (j : Spec (.of R) ⟶ C.left) [IsOpenImmersion j]
  (hj : Set.range j ⊆ divisorComplement K n p a)

include hj in
/-- Every affine image inside the complement maps into the canonical projective chart. -/
lemma affine_image_le_canonical_preimage : j ''ᵁ ⊤ ≤
    cubicProjectiveMorphism K n hn p q h a ⁻¹ᵁ
      chart K (Fin (n * 3 + 1 + 1)) (canonicalIndex.{0} n) := by
  rw [cubicProjectiveMorphism_preimage_chart]
  simpa only [finiteCubicOpen, cubicOpen, finiteCubicFamily] using
    affine_image_le_canonical K n hn p q h a j hj

/-- Chart sections pull back to the previously sealed map's actual defining sections. -/
lemma affine_canonical_projective_chartSection
    (z : chartRing K (Fin (n * 3 + 1 + 1)) (canonicalIndex.{0} n)) :
    (cubicProjectiveMorphism K n hn p q h a).appLE
      (chart K (Fin (n * 3 + 1 + 1)) (canonicalIndex.{0} n)) (j ''ᵁ ⊤)
      (affine_image_le_canonical_preimage K n hn p q h a j hj)
      (Proj.awayToSection (grading K (Fin (n * 3 + 1 + 1)))
        (MvPolynomial.X (canonicalIndex.{0} n)) z) =
      sectionProjectiveChartRingMap (polygonLine K n hn p q h a 3) (n * 3 + 1)
        (finiteCubicFamily K n hn p q h a) (canonicalIndex.{0} n) _
        (affine_image_le_canonical K n hn p q h a j hj) (cubicOpenScalars K _) z := by
  apply chartSection_evaluation_apply
  exact sectionProjectiveMorphism_onOpen (polygonLine K n hn p q h a 3) (n * 3 + 1)
    (finiteCubicFamily K n hn p q h a) (iSup_finiteCubicOpen K n hn p q h a)
    (C.hom.appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom) _ _
    (affine_image_le_canonical K n hn p q h a j hj)

/-- In affine coordinates the global pullback is exactly the sealed canonical chart map. -/
lemma affineCanonicalChartRingMap_projective
    (z : chartRing K (Fin (n * 3 + 1 + 1)) (canonicalIndex.{0} n)) :
    affineCanonicalChartRingMap K n hn p q h a j hj z =
      (Scheme.ΓSpecIso (.of R)).hom ((j.appIso ⊤).hom
        ((cubicProjectiveMorphism K n hn p q h a).appLE
          (chart K (Fin (n * 3 + 1 + 1)) (canonicalIndex.{0} n)) (j ''ᵁ ⊤)
          (affine_image_le_canonical_preimage K n hn p q h a j hj)
          (Proj.awayToSection (grading K (Fin (n * 3 + 1 + 1)))
            (MvPolynomial.X (canonicalIndex.{0} n)) z))) := by
  rw [affine_canonical_projective_chartSection K n hn p q h a j hj,
    affineCanonicalChartRingMap_apply]

end FLT.Mazur.PolygonCubicSections
