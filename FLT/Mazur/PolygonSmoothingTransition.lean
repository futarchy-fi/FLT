/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonSmoothingBranchOpens

/-!
# Coordinate transitions on the nonzero-parameter overlap

When the smoothing parameter is a unit, the two Laurent presentations are
related by z ↦ t/z. The transition is an involution and its spectrum gives
the actual commuting diagram between the original branch open immersions.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped LaurentPolynomial

namespace FLT.Mazur.PolygonSmoothing

variable {R : Type*} [CommRing R]

/-- The unit giving the opposite coordinate on the nonzero-parameter overlap. -/
def transitionUnit (a : Rˣ) : R[T;T⁻¹]ˣ where
  val := LaurentPolynomial.C (a : R) * LaurentPolynomial.T (-1)
  inv := LaurentPolynomial.C (↑a⁻¹ : R) * LaurentPolynomial.T 1
  val_inv := by
    rw [mul_mul_mul_comm, ← map_mul, ← LaurentPolynomial.T_add]
    simp
  inv_val := by
    rw [mul_mul_mul_comm, ← map_mul, ← LaurentPolynomial.T_add]
    simp

/-- The substitution z ↦ t/z on the actual Laurent algebra. -/
def transitionMap (a : Rˣ) : R[T;T⁻¹] →ₐ[R] R[T;T⁻¹] :=
  LaurentUnitPoints.evalUnit (transitionUnit a)

/-- The overlap transition retains all coefficients. -/
@[simp] theorem transitionMap_C (a : Rˣ) (r : R) :
    transitionMap a (LaurentPolynomial.C r) = LaurentPolynomial.C r :=
  LaurentUnitPoints.evalUnit_C _ _

/-- The positive Laurent variable becomes the parameter times the inverse variable. -/
@[simp] theorem transitionMap_pos (a : Rˣ) :
    transitionMap a (LaurentPolynomial.T 1) =
      LaurentPolynomial.C (a : R) * LaurentPolynomial.T (-1) := by
  simp [transitionMap, transitionUnit]

/-- The inverse variable becomes the inverse parameter times the positive variable. -/
@[simp] theorem transitionMap_neg (a : Rˣ) :
    transitionMap a (LaurentPolynomial.T (-1)) =
      LaurentPolynomial.C (↑a⁻¹ : R) * LaurentPolynomial.T 1 := by
  simp [transitionMap, transitionUnit]

/-- Changing branches twice fixes the full Laurent algebra. -/
theorem transitionMap_comp (a : Rˣ) :
    (transitionMap a).comp (transitionMap a) = AlgHom.id R _ := by
  apply LaurentUnitPoints.hom_ext <;>
    simp only [AlgHom.comp_apply, transitionMap_pos, transitionMap_neg, map_mul,
      transitionMap_C, AlgHom.id_apply] <;>
    rw [← mul_assoc, ← map_mul] <;> simp

/-- The actual algebra equivalence between the two branch presentations. -/
def transitionEquiv (a : Rˣ) : R[T;T⁻¹] ≃ₐ[R] R[T;T⁻¹] :=
  AlgEquiv.ofAlgHom (transitionMap a) (transitionMap a)
    (transitionMap_comp a) (transitionMap_comp a)

/-- The transition carries the original first chart presentation to the second. -/
theorem transitionMap_chart (a : Rˣ) :
    (transitionMap a).comp (leftLaurentMap (a : R)) =
      (leftLaurentMap (a : R)).comp (branchSwapMap (a : R)) := by
  apply chartRing_hom_ext (a : R)
  · simp
  · simp only [AlgHom.comp_apply, leftLaurentMap_right, map_mul, transitionMap_C,
      transitionMap_neg, branchSwapMap_right, leftLaurentMap_left]
    rw [← mul_assoc, ← map_mul]
    simp

/-- The coordinate transition on actual torus schemes. -/
def transitionIso (a : Rˣ) : branchTorus R ≅ branchTorus R :=
  Scheme.Spec.mapIso (transitionEquiv a).toRingEquiv.toCommRingCatIso.op

/-- The transition identifies the actual two branch morphisms over the unit-parameter chart. -/
@[reassoc] theorem transitionIso_left (a : Rˣ) :
    (transitionIso a).hom ≫ leftBranchOpen R (a : R) = rightBranchOpen R (a : R) := by
  change Spec.map _ ≫ (Spec.map _ ≫ Spec.map _) = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  change transitionMap a (leftPunctureToLaurent (a : R)
    (algebraMap (ChartRing (a : R)) _ z)) =
    leftPunctureToLaurent (a : R) (rightToLeftPuncture (a : R)
      (algebraMap (ChartRing (a : R)) _ z))
  rw [leftPunctureToLaurent_map, rightToLeftPuncture_map, leftPunctureToLaurent_map]
  exact DFunLike.congr_fun (transitionMap_chart a) z

end FLT.Mazur.PolygonSmoothing
