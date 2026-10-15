/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonFirstOrderCoordinateCharts
public import FLT.Mazur.LaurentScaledCoordinateIsomorphisms

/-!
# Full Laurent algebra automorphisms for first-order coordinate changes

The universal square-zero unit defines an automorphism of the entire
Laurent algebra. Composition adds vector fields and negation supplies the
inverse, retaining the coefficient ring and all first-order terms.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open LaurentPolynomial LaurentUnitPoints LaurentSquareZeroCoordinate PolygonChartScaling
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R]
local notation "S" => Ring R 1
local notation "L" => (S)[T;T⁻¹]
local notation "e" => parameter R 1

/-- Substitute the entire first-order coordinate, keeping the original coefficient ring. -/
def firstOrderLaurentHom (q : R[T;T⁻¹]) : (L) →ₐ[S] (L) :=
  evalUnit (firstOrderCoordinateUnit q)

/-- Substitution fixes every scalar coefficient. -/
theorem firstOrderLaurentHom_C (q : R[T;T⁻¹]) (s : S) :
    firstOrderLaurentHom q (C s) = C s := evalUnit_C _ _

/-- Substitution carries the universal unperturbed unit to the prescribed first-order unit. -/
theorem firstOrderLaurentHom_coordinate (q : R[T;T⁻¹]) :
    Units.map (firstOrderLaurentHom q).toMonoidHom (coordinateUnit (1 : (S)ˣ)) =
      firstOrderCoordinateUnit q := by
  apply Units.ext
  change firstOrderLaurentHom q (C 1 * T 1) = _
  rw [map_one, one_mul]
  exact (evalUnit_T _ 1).trans (congrArg Units.val (zpow_one _))

/-- The full substitution transports every second field by exact square-zero addition. -/
theorem firstOrderLaurentHom_unit (p q : R[T;T⁻¹]) :
    Units.map (firstOrderLaurentHom q).toMonoidHom (firstOrderCoordinateUnit p) =
      firstOrderCoordinateUnit (p + q) := by
  have hc : (firstOrderLaurentHom q).toRingHom.comp (C.comp (algebraMap R (S))) =
      C.comp (algebraMap R (S)) := by
    apply RingHom.ext
    intro r
    exact firstOrderLaurentHom_C q _
  change Units.map (firstOrderLaurentHom q).toRingHom.toMonoidHom
    (change (C.comp (algebraMap R (S))) (C (e)) _ p (coordinateUnit 1)) = _
  have hm := change_map (C.comp (algebraMap R (S))) (firstOrderLaurentHom q).toRingHom
    (C (e)) (by rw [← map_pow, parameter_pow R 1, map_zero]) p
    (coordinateUnit (1 : (S)ˣ))
  apply hm.trans
  rw [hc]
  change change (C.comp (algebraMap R (S))) (firstOrderLaurentHom q (C (e))) _ p
    (Units.map (firstOrderLaurentHom q).toMonoidHom (coordinateUnit 1)) = _
  simp only [firstOrderLaurentHom_C, firstOrderLaurentHom_coordinate]
  exact change_change _ _ _ p q _

/-- Composition of the actual Laurent algebra maps adds their fields. -/
theorem firstOrderLaurentHom_comp (p q : R[T;T⁻¹]) :
    (firstOrderLaurentHom q).comp (firstOrderLaurentHom p) =
      firstOrderLaurentHom (p + q) := by
  change (firstOrderLaurentHom q).comp (evalUnit (firstOrderCoordinateUnit p)) = _
  rw [evalUnit_natural, firstOrderLaurentHom_unit]
  rfl

/-- The zero field is exactly the identity on all Laurent functions. -/
theorem firstOrderLaurentHom_zero : firstOrderLaurentHom (0 : R[T;T⁻¹]) = AlgHom.id (S) (L) := by
  apply pointsEquiv.injective
  apply Units.ext
  change (firstOrderLaurentHom (0 : R[T;T⁻¹])) (T 1) = T 1
  rw [firstOrderLaurentHom, evalUnit_T, zpow_one, firstOrderCoordinateUnit_val,
    firstOrderLaurentCoordinate, map_zero, mul_zero, add_zero]

/-- The full first-order Laurent algebra automorphism, with inverse obtained by negation. -/
def firstOrderLaurentEquiv (q : R[T;T⁻¹]) : (L) ≃ₐ[S] (L) :=
  AlgEquiv.ofAlgHom (firstOrderLaurentHom q) (firstOrderLaurentHom (-q))
    (by rw [firstOrderLaurentHom_comp, neg_add_cancel, firstOrderLaurentHom_zero])
    (by rw [firstOrderLaurentHom_comp, add_neg_cancel, firstOrderLaurentHom_zero])

/-- Promotion retains the original substitution on every Laurent function. -/
theorem firstOrderLaurentEquiv_apply (q : R[T;T⁻¹]) (p : L) :
    firstOrderLaurentEquiv q p = firstOrderLaurentHom q p := rfl

/-- The full inverse is substitution by the negative field. -/
theorem firstOrderLaurentEquiv_symm_apply (q : R[T;T⁻¹]) (p : L) :
    (firstOrderLaurentEquiv q).symm p = firstOrderLaurentHom (-q) p := rfl

/-- The full scaled first-order substitution is also an algebra automorphism. -/
def firstOrderScaledLaurentEquiv (a : (S)ˣ) (q : R[T;T⁻¹]) : (L) ≃ₐ[S] (L) :=
  (PolygonScaledReciprocal.scalingEquiv a).trans (firstOrderLaurentEquiv q)

/-- Scaling and perturbation retain the exact original full unit in the substitution map. -/
theorem firstOrderScaledLaurentEquiv_toAlgHom (a : (S)ˣ) (q : R[T;T⁻¹]) :
    (firstOrderScaledLaurentEquiv a q).toAlgHom =
      evalUnit (Units.map (C : (S) →+* (L)).toMonoidHom a * firstOrderCoordinateUnit q) := by
  change (evalUnit (firstOrderCoordinateUnit q)).comp (PolygonScaledReciprocal.scaling a) = _
  exact evalUnit_scaling a _

end FLT.Mazur.PolygonInfinitesimalStages
