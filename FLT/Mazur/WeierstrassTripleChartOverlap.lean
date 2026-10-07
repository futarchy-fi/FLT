/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassChartOverlap

/-!
# Triple principal intersections of the integral cubic

In chart j, the intersection with charts k and l inverts the product of their
coordinates. Both principal overlaps restrict to this ring, and normalization
in chart k gives the cyclic transition to the next presentation.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (j k l : Fin 3)

/-- The simultaneous principal intersection of three charts, viewed from j. -/
abbrev TripleOverlap := Localization.Away (coord W j k * coord W j l)

/-- Universal coordinates on the triple intersection. -/
def tripleCoord (i : Fin 3) : TripleOverlap W j k l :=
  algebraMap (Coordinate W j) (TripleOverlap W j k l) (coord W j i)

@[simp] theorem tripleCoord_self : tripleCoord W j k l j = 1 := by
  simp only [tripleCoord, coord_self, map_one]

/-- Both coordinates inverted in the triple intersection are units. -/
theorem tripleCoord_units :
    IsUnit (tripleCoord W j k l k) ∧ IsUnit (tripleCoord W j k l l) := by
  apply IsUnit.mul_iff.mp
  change IsUnit (algebraMap (Coordinate W j) (TripleOverlap W j k l) (coord W j k) *
    algebraMap (Coordinate W j) (TripleOverlap W j k l) (coord W j l))
  rw [← map_mul]
  exact IsLocalization.Away.algebraMap_isUnit _

/-- Restriction of the j/k overlap to the triple intersection. -/
def tripleLeft : Overlap W j k →ₐ[R] TripleOverlap W j k l :=
  IsLocalization.Away.liftAlgHom (coord W j k)
    (f := IsScalarTower.toAlgHom R (Coordinate W j) (TripleOverlap W j k l))
    (tripleCoord_units W j k l).1

/-- Restriction of the j/l overlap to the triple intersection. -/
def tripleRight : Overlap W j l →ₐ[R] TripleOverlap W j k l :=
  IsLocalization.Away.liftAlgHom (coord W j l)
    (f := IsScalarTower.toAlgHom R (Coordinate W j) (TripleOverlap W j k l))
    (tripleCoord_units W j k l).2

@[simp] theorem tripleLeft_coord (i : Fin 3) :
    tripleLeft W j k l (overlapCoord W j k i) = tripleCoord W j k l i :=
  IsLocalization.Away.lift_eq _ (tripleCoord_units W j k l).1 _

@[simp] theorem tripleRight_coord (i : Fin 3) :
    tripleRight W j k l (overlapCoord W j l i) = tripleCoord W j k l i :=
  IsLocalization.Away.lift_eq _ (tripleCoord_units W j k l).2 _

/-- The reciprocal of coordinate k on the simultaneous intersection. -/
def tripleInverse : TripleOverlap W j k l :=
  tripleLeft W j k l (overlapInverse W j k)

@[simp] theorem tripleInverse_mul :
    tripleInverse W j k l * tripleCoord W j k l k = 1 := by
  simpa only [map_mul, map_one, tripleLeft_coord, tripleInverse] using
    congrArg (tripleLeft W j k l) (overlapInverse_mul W j k)

/-- The normalizing inverse remains a unit. -/
theorem tripleInverse_isUnit : IsUnit (tripleInverse W j k l) :=
  (overlapInverse_isUnit W j k).map (tripleLeft W j k l)

/-- The coordinates in the next chart, on the full triple intersection. -/
def tripleTransitionBase : Coordinate W k →ₐ[R] TripleOverlap W j k l :=
  (tripleLeft W j k l).comp (transitionBase W j k)

@[simp] theorem tripleTransitionBase_coord (i : Fin 3) :
    tripleTransitionBase W j k l (coord W k i) =
      tripleInverse W j k l * tripleCoord W j k l i := by
  simp only [tripleTransitionBase, AlgHom.comp_apply, transitionBase_coord,
    map_mul, tripleLeft_coord, tripleInverse]

/-- The two denominators in the next presentation are invertible. -/
theorem tripleTransitionBase_isUnit :
    IsUnit (tripleTransitionBase W j k l (coord W k l * coord W k j)) := by
  rw [map_mul, tripleTransitionBase_coord, tripleTransitionBase_coord,
    tripleCoord_self, mul_one]
  exact ((tripleInverse_isUnit W j k l).mul (tripleCoord_units W j k l).2).mul
    (tripleInverse_isUnit W j k l)

/-- Cyclic chart change on the entire triple principal intersection. -/
def tripleTransition : TripleOverlap W k l j →ₐ[R] TripleOverlap W j k l :=
  IsLocalization.Away.liftAlgHom (coord W k l * coord W k j)
    (tripleTransitionBase_isUnit W j k l)

@[simp] theorem tripleTransition_coord (i : Fin 3) :
    tripleTransition W j k l (tripleCoord W k l j i) =
      tripleInverse W j k l * tripleCoord W j k l i := by
  change IsLocalization.Away.lift _ (tripleTransitionBase_isUnit W j k l)
    (algebraMap _ _ (coord W k i)) = _
  rw [IsLocalization.Away.lift_eq]
  exact tripleTransitionBase_coord W j k l i

/-- Maps out of a triple overlap are determined by the three coordinates. -/
@[ext] theorem tripleOverlap_hom_ext
    (f g : TripleOverlap W j k l →ₐ[R] S)
    (h : ∀ i, f (tripleCoord W j k l i) = g (tripleCoord W j k l i)) : f = g := by
  apply IsLocalization.algHom_ext (Submonoid.powers (coord W j k * coord W j l))
  exact hom_ext W j _ _ h

end FLT.Mazur.WeierstrassIntegralChart
