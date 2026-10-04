/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCubicTorusPullback
public import FLT.Mazur.PolygonCubicTorusNumerators
public import FLT.Mazur.ProjectiveChartPointMembership
public import FLT.Mazur.AffineImageSectionTransport

/-!
# Projective chart membership on the polygon tori

The computed Laurent ring map presents the actual cubic morphism on each
torus. Its linear coordinates distinguish the torus components.
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
  (a : Fin n → Kˣ)

/-- The projective index of an interpolation coordinate. -/
def interpolationIndex (n : ℕ) (i : Fin n) (k : Fin 3) : Fin (n * 3 + 1 + 1) :=
  (cubicCoordinateEquiv.{0} n).symm (.inr ⟨(i, k)⟩)

/-- Spec of the Laurent ring map recovers the actual cubic map on a torus. -/
@[reassoc]
lemma torusChartRingMap_spec (i : Fin n) :
    Spec.map (CommRingCat.ofHom (torusChartRingMap K n hn p q h a i)) ≫
      ProjectiveSpace.chartMap K _ (interiorIndex.{0} n) =
        (torusToComponent K ≫ componentι K n i ≫ p).left ≫
          cubicProjectiveMorphism K n hn p q h a := by
  let := torus_isOpenImmersion K n hn p q h i
  let j := (torusToComponent K ≫ componentι K n i ≫ p).left
  have ho := sectionProjectiveMorphism_onOpen (polygonLine K n hn p q h a 3)
    (n * 3 + 1) (finiteCubicFamily K n hn p q h a)
    (iSup_finiteCubicOpen K n hn p q h a)
    (C.hom.appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom)
    (interiorIndex.{0} n) (j ''ᵁ ⊤) (torus_image_le_interior K n hn p q h a i)
  change (j ''ᵁ ⊤).ι ≫ cubicProjectiveMorphism K n hn p q h a =
    sectionProjectiveChartMorphism (polygonLine K n hn p q h a 3) (n * 3 + 1)
      (finiteCubicFamily K n hn p q h a) (interiorIndex.{0} n) (j ''ᵁ ⊤)
      (torus_image_le_interior K n hn p q h a i) (cubicOpenScalars K _) at ho
  rw [torusChartRingMap_def]
  change Spec.map (CommRingCat.ofHom ((Scheme.ΓSpecIso (.of (LaurentPolynomial K))).hom.hom.comp
    ((j.appIso ⊤).hom.hom.comp _))) ≫ _ = _
  rw [AffineImageSectionTransport.spec_transport, Category.assoc, Category.assoc]
  change AffineImageSectionTransport.factor j ≫
    sectionProjectiveChartMorphism (polygonLine K n hn p q h a 3) (n * 3 + 1)
      (finiteCubicFamily K n hn p q h a) (interiorIndex.{0} n) (j ''ᵁ ⊤)
      (torus_image_le_interior K n hn p q h a i) (cubicOpenScalars K _) = _
  rw [← ho, ← Category.assoc, AffineImageSectionTransport.factor_ι]

/-- A linear coordinate is one on its own torus and zero on every other torus. -/
lemma torusChartRingMap_linear (i j : Fin n) :
    torusChartRingMap K n hn p q h a i
      (ProjectiveSpace.coordinate K _ (interiorIndex.{0} n) (interpolationIndex n j 1)) =
        if i = j then 1 else 0 := by
  rw [interpolationIndex, torusChartRingMap_interpolation]
  by_cases hij : i = j <;> simp [interpolationLaurent, cubicDelta, hij]

/-- Membership in a linear-coordinate chart detects the torus component. -/
lemma torus_image_mem_linear_iff (i j : Fin n) (x : Spec (.of (LaurentPolynomial K))) :
    cubicProjectiveMorphism K n hn p q h a
      ((torusToComponent K ≫ componentι K n i ≫ p).left x) ∈
        ProjectiveSpace.chart K _ (interpolationIndex n j 1) ↔ i = j := by
  change ((torusToComponent K ≫ componentι K n i ≫ p).left ≫
    cubicProjectiveMorphism K n hn p q h a) x ∈ _ ↔ _
  rw [← torusChartRingMap_spec]
  change (Spec.map (CommRingCat.ofHom (torusChartRingMap K n hn p q h a i)) ≫
    ProjectiveSpace.chartMap K _ (interiorIndex.{0} n)) x ∈ _ ↔ _
  rw [ProjectiveSpace.spec_chartMap_mem_iff,
    torusChartRingMap_linear]
  split_ifs with hij
  · exact iff_of_true (fun hh ↦ x.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hh isUnit_one)) hij
  · simp [hij]

end FLT.Mazur.PolygonCubicSections
