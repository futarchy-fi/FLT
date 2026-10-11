/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonSmoothingCoefficientBranches
public import FLT.Mazur.PolygonSmoothingCoordinateIdeal
public import Mathlib.RingTheory.Polynomial.Basic

/-!
# Explicit coefficient maps of arithmetic node rings

The polynomial quotient presentation makes the original coefficient map
surjective whenever its base map is surjective, and computes its exact kernel.
The construction agrees with the existing tensor coefficient projection.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.PolygonSmoothing

set_option backward.isDefEq.respectTransparency false

universe u

variable {R S : Type u} [CommRing R] [CommRing S]
  (f : R →+* S) (t : R) (s : S) (hs : f t = s)

include hs in
/-- Coefficient substitution preserves the actual equation with the specified parameter. -/
theorem relationIdeal_map_parameter :
    (relationIdeal t).map (MvPolynomial.map f) = relationIdeal s := by
  simp only [relationIdeal, Ideal.map_span, Set.image_singleton, relation,
    map_sub, map_mul, MvPolynomial.map_X, MvPolynomial.map_C, hs]

/-- The original coefficient substitution on polynomial representatives. -/
def ringMap : ChartRing t →+* ChartRing s :=
  Ideal.quotientMap _ (MvPolynomial.map f)
    (Ideal.map_le_iff_le_comap.mp (relationIdeal_map_parameter f t s hs).le)

/-- The specified map acts on every polynomial representative by coefficient substitution. -/
@[simp] theorem ringMap_mk (p : MvPolynomial (Fin 2) R) :
    ringMap f t s hs (Ideal.Quotient.mk _ p) =
      Ideal.Quotient.mk _ (MvPolynomial.map f p) := rfl

/-- The first original branch coordinate is unchanged. -/
@[simp] theorem ringMap_left :
    ringMap f t s hs (leftCoordinate t) = leftCoordinate s := by
  simp only [leftCoordinate, ringMap_mk, MvPolynomial.map_X]

/-- The second original branch coordinate is unchanged. -/
@[simp] theorem ringMap_right :
    ringMap f t s hs (rightCoordinate t) = rightCoordinate s := by
  simp only [rightCoordinate, ringMap_mk, MvPolynomial.map_X]

/-- Every original coefficient is sent by the given base map. -/
@[simp] theorem ringMap_scalar (r : R) :
    ringMap f t s hs (algebraMap R (ChartRing t) r) =
      algebraMap S (ChartRing s) (f r) := by
  change Ideal.Quotient.mk _ (MvPolynomial.map f (MvPolynomial.C r)) = _
  rw [MvPolynomial.map_C]
  rfl

/-- The original coordinate ideal has exactly the specified image ideal. -/
theorem ringMap_coordinateIdeal :
    (coordinateIdeal t).map (ringMap f t s hs) = coordinateIdeal s := by
  simp only [coordinateIdeal, Ideal.map_span, Set.image_insert_eq,
    Set.image_singleton, ringMap_left, ringMap_right]

/-- Surjective coefficient changes give surjective actual node-ring maps. -/
theorem ringMap_surjective (hf : Function.Surjective f) :
    Function.Surjective (ringMap f t s hs) :=
  Ideal.quotientMap_surjective ((MvPolynomial.map_surjective_iff f).mpr hf)

/-- The kernel is exactly the original coefficient kernel extended to the node ring. -/
theorem ringMap_ker (hf : Function.Surjective f) :
    RingHom.ker (ringMap f t s hs) = (RingHom.ker f).map (algebraMap R (ChartRing t)) := by
  rw [ringMap, Ideal.quotientMap, Ideal.ker_quotient_lift, ← RingHom.comap_ker,
    Ideal.mk_ker, ← relationIdeal_map_parameter f t s hs,
    Ideal.comap_map_of_surjective _ ((MvPolynomial.map_surjective_iff f).mpr hf),
    ← RingHom.ker_eq_comap_bot, MvPolynomial.ker_map, Ideal.map_sup,
    Ideal.map_quotient_self, bot_sup_eq, Ideal.map_map]
  rfl

/-- The polynomial construction is the original tensor coefficient map. -/
theorem ringMap_eq_coefficientMap [Algebra R S] :
    ringMap (algebraMap R S) t (algebraMap R S t) rfl = coefficientMap R S t := by
  let g : ChartRing t →ₐ[R] ChartRing (algebraMap R S t) :=
    { ringMap (algebraMap R S) t (algebraMap R S t) rfl with
      commutes' r := by
        exact (ringMap_scalar ..).trans (IsScalarTower.algebraMap_apply R S _ r).symm }
  exact congrArg AlgHom.toRingHom
    (chartRing_hom_ext t g (coefficientAlgHom R S t)
      (by
        exact (ringMap_left (algebraMap R S) t _ rfl).trans
          (coefficientMap_left R S t).symm)
      (by
        exact (ringMap_right (algebraMap R S) t _ rfl).trans
          (coefficientMap_right R S t).symm))

end FLT.Mazur.PolygonSmoothing
