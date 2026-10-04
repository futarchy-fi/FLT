/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProjectiveProductChartOverlaps

/-!
# Compatibility of actual projective chart morphisms

The homogeneous overlap ring is the localization of one chart at the other
coordinate. A unit transition ratio extends the first ring map across this
localization. Coordinate change identifies its restriction to the second chart.
-/

open CategoryTheory AlgebraicGeometry
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.ProjectiveSpace
attribute [local instance] MvPolynomial.gradedAlgebra
variable (R S : Type u) [CommRing R] [CommRing S] (ι : Type)

/-- Compatible coordinate values extend to a map from the actual homogeneous overlap ring. -/
theorem exists_overlapRingMap (i j : ι)
    (f : chartRing R ι i →+* S) (g : chartRing R ι j →+* S)
    (hR : ∀ a, f (chartScalars R ι i a) = g (chartScalars R ι j a))
    (hX : ∀ k, f (coordinate R ι i k) =
      g (coordinate R ι j k) * f (coordinate R ι i j))
    (hu : IsUnit (f (coordinate R ι i j))) :
    ∃ l : overlapRing R ι i j →+* S,
      l.comp (chartOverlapLeft R ι i j).toRingHom = f ∧
        l.comp (chartOverlapRight R ι i j).toRingHom = g := by
  let := (toOverlap R ι i j).toAlgebra
  let := overlap_isLocalization R ι i j
  let l : overlapRing R ι i j →+* S := IsLocalization.Away.lift (coordinate R ι i j) hu
  have hl (x : chartRing R ι i) : l (chartOverlapLeft R ι i j x) = f x :=
    IsLocalization.Away.lift_eq (coordinate R ι i j) hu x
  refine ⟨l, RingHom.ext hl, ?_⟩
  apply chartRing_hom_ext R ι j
  · intro a
    change l (chartOverlapRight R ι i j (chartScalars R ι j a)) = _
    have he : chartOverlapRight R ι i j (chartScalars R ι j a) =
        chartOverlapLeft R ι i j (chartScalars R ι i a) :=
      ((chartOverlapRight R ι i j).commutes a).trans
        ((chartOverlapLeft R ι i j).commutes a).symm
    rw [he, hl]
    exact hR a
  · intro k
    apply hu.mul_right_cancel
    change l (chartOverlapRight R ι i j (coordinate R ι j k)) *
      f (coordinate R ι i j) = g (coordinate R ι j k) * f (coordinate R ι i j)
    rw [← hl (coordinate R ι i j), ← map_mul, ← chartOverlap_coordinate, hl, hX, hl]

/-- Compatible chart ring maps induce equal actual morphisms to projective space. -/
theorem chartMaps_eq_of_coordinates (i j : ι)
    (f : chartRing R ι i →+* S) (g : chartRing R ι j →+* S)
    (hR : ∀ a, f (chartScalars R ι i a) = g (chartScalars R ι j a))
    (hX : ∀ k, f (coordinate R ι i k) =
      g (coordinate R ι j k) * f (coordinate R ι i j))
    (hu : IsUnit (f (coordinate R ι i j))) :
    Spec.map (CommRingCat.ofHom f) ≫ chartMap R ι i =
      Spec.map (CommRingCat.ofHom g) ≫ chartMap R ι j := by
  obtain ⟨l, hl, hr⟩ := exists_overlapRingMap R S ι i j f g hR hX hu
  rw [← hl, ← hr]
  change Spec.map (CommRingCat.ofHom (chartOverlapLeft R ι i j).toRingHom ≫
      CommRingCat.ofHom l) ≫ _ =
    Spec.map (CommRingCat.ofHom (chartOverlapRight R ι i j).toRingHom ≫
      CommRingCat.ofHom l) ≫ _
  rw [Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc]
  exact congrArg (fun z ↦ Spec.map (CommRingCat.ofHom l) ≫ z)
    (chartOverlapIsPullback R ι i j).w

end FLT.Mazur.ProjectiveSpace
