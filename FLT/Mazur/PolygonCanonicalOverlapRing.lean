/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineIntersectionRestriction
public import FLT.Mazur.PolygonCanonicalTorusTransition

/-!
# The canonical cubic identity in an actual affine overlap ring

A concrete affine pullback square transports the canonical/torus identity to
its two ring maps. The split and one-gon punctured localization squares supply
such pullbacks without any comparison of pulled-back line modules.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.PolygonCubicSections
open PolygonPinching AffinePullbackIntersection ProjectiveLineMarkedSectionTransition
attribute [local instance] MvPolynomial.gradedAlgebra
variable (K : Type u) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
  (a : Fin n → Kˣ) {R S : Type u} [CommRing R] [CommRing S]
  (j : Spec (.of R) ⟶ C.left) [IsOpenImmersion j]
  (hj : Set.range j ⊆ divisorComplement K n p a)

/-- Cross multiplication in the exact ring of an actual canonical/torus overlap. -/
lemma canonical_overlap_ring (i : Fin n) (f : R →+* S)
    (g : LaurentPolynomial K →+* S)
    (H : IsPullback (Spec.map (CommRingCat.ofHom f)) (Spec.map (CommRingCat.ofHom g))
      j (torusToComponent K ≫ componentι K n i ≫ p).left)
    (k : Fin (n * 3 + 1 + 1)) :
    f (affineCanonicalChartRingMap K n hn p q h a j hj
      (ProjectiveSpace.coordinate K (Fin (n * 3 + 1 + 1)) (canonicalIndex.{u} n) k)) *
      g (torusChartRingMap K n hn p q h a i
        (ProjectiveSpace.coordinate K (Fin (n * 3 + 1 + 1)) (interiorIndex.{u} n)
          (canonicalIndex.{u} n))) =
      g (torusChartRingMap K n hn p q h a i
        (ProjectiveSpace.coordinate K (Fin (n * 3 + 1 + 1)) (interiorIndex.{u} n) k)) := by
  let := torus_isOpenImmersion K n hn p q h i
  let e := sectionsIso _ _ _ _ H
  have he := congrArg e.hom.hom (canonical_torus_crossMultiply K n hn p q h a j hj i k)
  rw [map_mul] at he
  dsimp only [canonicalCoordinateSection, torusCoordinateSection] at he
  change (sectionsIso _ _ _ _ H).hom
      (C.left.presheaf.map (homOfLE inf_le_left).op
        ((j.appIso ⊤).inv ((Scheme.ΓSpecIso (.of R)).inv _))) *
    (sectionsIso _ _ _ _ H).hom
      (C.left.presheaf.map (homOfLE inf_le_right).op
        (((torusToComponent K ≫ componentι K n i ≫ p).left.appIso ⊤).inv
          ((Scheme.ΓSpecIso (.of (LaurentPolynomial K))).inv _))) =
    (sectionsIso _ _ _ _ H).hom
      (C.left.presheaf.map (homOfLE inf_le_right).op
        (((torusToComponent K ≫ componentι K n i ≫ p).left.appIso ⊤).inv
          ((Scheme.ΓSpecIso (.of (LaurentPolynomial K))).inv _))) at he
  erw [sectionsIso_restrict_spec (H := H), sectionsIso_restrict_right_spec (H := H),
    sectionsIso_restrict_right_spec (H := H)] at he
  exact he

end FLT.Mazur.PolygonCubicSections
