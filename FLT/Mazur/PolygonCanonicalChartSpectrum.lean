/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCanonicalChartPullback
public import FLT.Mazur.AffineImageSectionTransport

/-!
# The spectrum chart map is the restricted cubic morphism

The canonical chart ring map, transported through the Gamma-Spec and
projective chart isomorphisms, gives precisely the global cubic morphism
on every affine open in the divisor complement.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.PolygonCubicSections
open FCurve PolygonPinching PolygonPowerNodeEndpoints
attribute [local instance] MvPolynomial.gradedAlgebra
variable (K : Type) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
  (a : Fin n → Kˣ) {R : Type} [CommRing R]
  (j : Spec (.of R) ⟶ C.left) [IsOpenImmersion j]
  (hj : Set.range j ⊆ divisorComplement K n p a)

/-- Passing to Spec and the standard projective chart recovers the actual morphism. -/
@[reassoc]
lemma affineCanonicalChartRingMap_spec :
    Spec.map (CommRingCat.ofHom (affineCanonicalChartRingMap K n hn p q h a j hj)) ≫
      ProjectiveSpace.chartMap K _ (canonicalIndex.{0} n) =
        j ≫ cubicProjectiveMorphism K n hn p q h a := by
  have ho := sectionProjectiveMorphism_onOpen (polygonLine K n hn p q h a 3)
    (n * 3 + 1) (finiteCubicFamily K n hn p q h a)
    (iSup_finiteCubicOpen K n hn p q h a)
    (C.hom.appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom)
    (canonicalIndex.{0} n) (j ''ᵁ ⊤) (affine_image_le_canonical K n hn p q h a j hj)
  change (j ''ᵁ ⊤).ι ≫ cubicProjectiveMorphism K n hn p q h a =
    sectionProjectiveChartMorphism (polygonLine K n hn p q h a 3) (n * 3 + 1)
      (finiteCubicFamily K n hn p q h a) (canonicalIndex.{0} n) (j ''ᵁ ⊤)
      (affine_image_le_canonical K n hn p q h a j hj) (cubicOpenScalars K _) at ho
  rw [affineCanonicalChartRingMap_def, AffineImageSectionTransport.spec_transport]
  rw [Category.assoc, Category.assoc]
  change AffineImageSectionTransport.factor j ≫
    sectionProjectiveChartMorphism (polygonLine K n hn p q h a 3) (n * 3 + 1)
      (finiteCubicFamily K n hn p q h a) (canonicalIndex.{0} n) (j ''ᵁ ⊤)
      (affine_image_le_canonical K n hn p q h a j hj) (cubicOpenScalars K _) = _
  rw [← ho, ← Category.assoc, AffineImageSectionTransport.factor_ι]

end FLT.Mazur.PolygonCubicSections
