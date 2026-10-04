/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCanonicalChartRing
public import FLT.Mazur.PolygonCubicTorusChart

/-!
# Ring transition from canonical node coordinates to computed torus coordinates

Transport the two actual affine chart ring maps back to regular functions.
On their intersection their coordinates satisfy a cross-multiplied identity.
This uses the proved torus map without converting the component pullback module.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
open scoped Polynomial LaurentPolynomial
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.PolygonCubicSections
open FCurve PolygonPinching PolygonPowerNodeEndpoints ProjectiveLineMarkedSectionTransition
attribute [local instance] MvPolynomial.gradedAlgebra
variable (K : Type u) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
  (a : Fin n → Kˣ)

/-- The computed Laurent chart map, expressed in the actual image section ring. -/
def torusCoordinateSection (i : Fin n) (k : Fin (n * 3 + 1 + 1)) :
    let := torus_isOpenImmersion K n hn p q h i
    Γ(C.left, (torusToComponent K ≫ componentι K n i ≫ p).left ''ᵁ ⊤) :=
  let := torus_isOpenImmersion K n hn p q h i
  (((torusToComponent K ≫ componentι K n i ≫ p).left.appIso ⊤).inv)
    (laurentRing K (torusChartRingMap K n hn p q h a i
      (ProjectiveSpace.coordinate K (Fin (n * 3 + 1 + 1)) (interiorIndex.{u} n) k)))

/-- The torus ring coordinate is the existing section ratio, with only ring isomorphisms used. -/
lemma torusCoordinateSection_eq (i : Fin n) (k : Fin (n * 3 + 1 + 1)) :
    let := torus_isOpenImmersion K n hn p q h i
    torusCoordinateSection K n hn p q h a i k =
      sectionRatioOn (polygonLine K n hn p q h a 3)
        (finiteCubicFamily K n hn p q h a (interiorIndex.{u} n)) _
        (torus_image_le_interior K n hn p q h a i) (finiteCubicFamily K n hn p q h a k) := by
  let := torus_isOpenImmersion K n hn p q h i
  dsimp only [torusCoordinateSection]
  rw [torusChartRingMap_apply, RingEquiv.apply_symm_apply]
  rw [← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply]
  exact sectionProjectiveChartRingMap_coordinate _ _ _ _ _ _ _ _

/-- The same ring section has its computed interpolation Laurent expression. -/
lemma torusCoordinateSection_polynomial (i : Fin n) (k : CubicIndex.{u} n) :
    let := torus_isOpenImmersion K n hn p q h i
    torusCoordinateSection K n hn p q h a i ((cubicCoordinateEquiv.{u} n).symm k) =
      (((torusToComponent K ≫ componentι K n i ≫ p).left.appIso ⊤).inv)
        (laurentRing K (Polynomial.toLaurent
          (((sectionEquiv K n hn p q h a 2 (cubicFamily K n hn p q h a k)).val i).val) *
            LaurentPolynomial.T (-1))) := by
  let := torus_isOpenImmersion K n hn p q h i
  dsimp only [torusCoordinateSection]
  rw [torusChartRingMap_coordinate, RingEquiv.apply_symm_apply, torusRatio_eq]

/-- The node numerator retains the self-incidence cubic contribution on the common open. -/
lemma torusCoordinateSection_node (i : Fin n) :
    let := torus_isOpenImmersion K n hn p q h i
    torusCoordinateSection K n hn p q h a i
        ((cubicCoordinateEquiv.{u} n).symm (.inr ⟨(i, 0)⟩)) =
      (((torusToComponent K ≫ componentι K n i ≫ p).left.appIso ⊤).inv)
        (laurentRing K (LaurentPolynomial.T (-1) +
          LaurentPolynomial.C (weight K n a 3 i * cubicDelta K n i 0 0 ((finRotate n).symm i)) *
            LaurentPolynomial.T 2)) := by
  let := torus_isOpenImmersion K n hn p q h i
  have he := torusChartRingMap_coordinate K n hn p q h a i (.inr ⟨(i, 0)⟩)
  rw [torusRatio_node, RingEquiv.symm_apply_apply] at he
  exact congrArg (fun z ↦
    (((torusToComponent K ≫ componentι K n i ≫ p).left.appIso ⊤).inv)
      (laurentRing K z)) he

variable {R : Type u} [CommRing R] (j : Spec (.of R) ⟶ C.left) [IsOpenImmersion j]
  (hj : Set.range j ⊆ divisorComplement K n p a)

/-- The canonical chart coordinate, transported from its exact affine coordinate ring. -/
def canonicalCoordinateSection (k : Fin (n * 3 + 1 + 1)) : Γ(C.left, j ''ᵁ ⊤) :=
  (j.appIso ⊤).inv ((Scheme.ΓSpecIso (.of R)).inv
    (affineCanonicalChartRingMap K n hn p q h a j hj
      (ProjectiveSpace.coordinate K (Fin (n * 3 + 1 + 1)) (canonicalIndex.{u} n) k)))

/-- The canonical ring coordinate retains its genuine section ratio. -/
lemma canonicalCoordinateSection_eq (k : Fin (n * 3 + 1 + 1)) :
    canonicalCoordinateSection K n hn p q h a j hj k =
      sectionRatioOn (polygonLine K n hn p q h a 3)
        (finiteCubicFamily K n hn p q h a (canonicalIndex.{u} n)) _
        (affine_image_le_canonical K n hn p q h a j hj)
        (finiteCubicFamily K n hn p q h a k) := by
  unfold canonicalCoordinateSection
  rw [affineCanonicalChartRingMap_apply]
  have hc {A B : CommRingCat.{u}} (e : A ≅ B) (z : A) : e.inv (e.hom z) = z :=
    congrArg (fun f ↦ f.hom z) e.hom_inv_id
  rw [hc, hc]
  exact sectionProjectiveChartRingMap_coordinate _ _ _ _ _ _ _ _

/-- On the common open, the actual canonical coordinate times the computed torus
denominator equals the computed torus numerator. No component-module transport occurs. -/
lemma canonical_torus_crossMultiply (i : Fin n) (k : Fin (n * 3 + 1 + 1)) :
    let := torus_isOpenImmersion K n hn p q h i
    let U := j ''ᵁ ⊤
    let V := (torusToComponent K ≫ componentι K n i ≫ p).left ''ᵁ ⊤
    C.left.presheaf.map (homOfLE (show U ⊓ V ≤ U from inf_le_left)).op
        (canonicalCoordinateSection K n hn p q h a j hj k) *
      C.left.presheaf.map (homOfLE (show U ⊓ V ≤ V from inf_le_right)).op
        (torusCoordinateSection K n hn p q h a i (canonicalIndex.{u} n)) =
      C.left.presheaf.map (homOfLE (show U ⊓ V ≤ V from inf_le_right)).op
        (torusCoordinateSection K n hn p q h a i k) := by
  let := torus_isOpenImmersion K n hn p q h i
  dsimp only
  rw [canonicalCoordinateSection_eq, torusCoordinateSection_eq, torusCoordinateSection_eq,
    sectionRatioOn_restrict, sectionRatioOn_restrict, sectionRatioOn_restrict, mul_comm]
  exact sectionRatioOn_change _ _ _ _ _ _ _

end FLT.Mazur.PolygonCubicSections
