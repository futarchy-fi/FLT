/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonSmoothingSquareZeroShear
public import FLT.Mazur.LaurentSquareZeroAutomorphism

/-!
# Full puncture equations of square-zero node corrections

The corrected puncture carries its entire Laurent vector field. The opposite
puncture is unchanged as a morphism of schemes, not only on reduced points.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.PolygonSmoothing
open LaurentPolynomial
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (t e : R) (he : e ^ 2 = 0) (het : e * t = 0)
local notation "A" => ChartRing t
local notation "L" => R[T;T⁻¹]

include het in
/-- Any scalar annihilating the correction fixes all weighted Laurent functions. -/
theorem squareZeroSubst_smoothing (q z : L) :
    C t * LaurentSquareZeroAutomorphism.subst e he q z = C t * z := by
  apply LaurentWeightedInverse.weighted_hom_of_sub_mem e t (by rwa [mul_comm])
    (LaurentSquareZeroAutomorphism.subst e he q) (AlgHom.id R L) ?_ z
  rw [LaurentSquareZeroAutomorphism.subst_T, AlgHom.id_apply, add_sub_cancel_left,
    Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton]
  exact ⟨q, rfl⟩

/-- The first complete Laurent restriction is the specified coordinate correction. -/
theorem squareZeroShear_leftLaurent (p : A) :
    (leftLaurentMap t).comp (squareZeroShear t e het p) =
      (LaurentSquareZeroAutomorphism.subst e he (T 1 * leftLaurentMap t p)).comp
        (leftLaurentMap t) := by
  apply chartRing_hom_ext t
  · simp only [AlgHom.comp_apply, squareZeroShear_left, map_add, map_mul,
      leftLaurentMap_left, AlgHom.commutes, C_eq_algebraMap,
      LaurentSquareZeroAutomorphism.subst_T]
    ring
  · simp only [AlgHom.comp_apply, squareZeroShear_right, leftLaurentMap_right, map_mul]
    rw [show LaurentSquareZeroAutomorphism.subst e he (T 1 * leftLaurentMap t p) (C t) =
      C t from (LaurentSquareZeroAutomorphism.subst e he _).commutes t]
    exact (squareZeroSubst_smoothing t e he het _ _).symm

/-- The opposite full Laurent restriction is fixed, including every nilpotent coefficient. -/
theorem squareZeroShear_rightLaurent (p : A) :
    ((leftLaurentMap t).comp (branchSwapMap t)).comp (squareZeroShear t e het p) =
      (leftLaurentMap t).comp (branchSwapMap t) := by
  apply chartRing_hom_ext t
  · simp only [AlgHom.comp_apply, squareZeroShear_left, map_add, map_mul,
      branchSwapMap_left, leftLaurentMap_right, AlgHom.commutes]
    change C t * T (-1) + C e * (C t * T (-1)) * _ = C t * T (-1)
    rw [← mul_assoc (C e), ← map_mul, het, map_zero, zero_mul, zero_mul, add_zero]
  · simp only [AlgHom.comp_apply, squareZeroShear_right]

/-- The full node correction as an isomorphism of schemes. -/
def squareZeroShearIso (p : A) : chart R t ≅ chart R t :=
  Scheme.Spec.mapIso (squareZeroShearEquiv t e he het p).toRingEquiv.toCommRingCatIso.op

/-- The entire corrected puncture square commutes on spectra. -/
@[reassoc] theorem squareZeroShearIso_left (p : A) :
    leftBranchOpen R t ≫ (squareZeroShearIso t e he het p).hom =
      Spec.map (CommRingCat.ofHom
        (LaurentSquareZeroAutomorphism.subst e he (T 1 * leftLaurentMap t p)).toRingHom) ≫
          leftBranchOpen R t := by
  rw [leftBranchOpen_eq_spec]
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg Spec.map (CommRingCat.hom_ext
    (congrArg AlgHom.toRingHom (squareZeroShear_leftLaurent t e he het p)))

/-- The opposite original puncture map is unchanged by the whole node isomorphism. -/
@[reassoc] theorem squareZeroShearIso_right (p : A) :
    rightBranchOpen R t ≫ (squareZeroShearIso t e he het p).hom = rightBranchOpen R t := by
  rw [rightBranchOpen_eq_spec]
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  exact congrArg Spec.map (CommRingCat.hom_ext
    (congrArg AlgHom.toRingHom (squareZeroShear_rightLaurent t e het p)))

/-- The correction keeps the original coefficient structure on the entire node. -/
@[reassoc] theorem squareZeroShearIso_base (p : A) :
    (squareZeroShearIso t e he het p).hom ≫ chartStructure R t = chartStructure R t := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  exact congrArg Spec.map (CommRingCat.hom_ext (squareZeroShear t e het p).comp_algebraMap)

end FLT.Mazur.PolygonSmoothing
