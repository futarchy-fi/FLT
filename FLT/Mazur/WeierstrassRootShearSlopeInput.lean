/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSlopeLaurentCubic
public import FLT.Mazur.WeierstrassRootShearSmoothParameter
public import FLT.Mazur.WeierstrassVariableChangeAffineRestriction
public import FLT.Mazur.WeierstrassModificationXScaleOneEquiv
public import FLT.Mazur.WeierstrassModificationXMorphism

/-!
# Original cubic functions identify the root-sheared smooth input

The equality uses both original affine functions, including the root shift
in Y. It compares the whole morphism through the proper cubic isomorphism.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory WeierstrassCurve
namespace FLT.Mazur.WeierstrassIntegralChart
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] (a : Rˣ)
local notation "U" => splitNodalEquation a
local notation "P" => SlopeOpen (a : R)
local notation "z" => slopeZ (a : R)
local notation "A" => algebraMap R P (a : R)

/-- The split affine slope map is induced by the actual incidence contraction. -/
@[irreducible] def splitSlopeAffineInput : Coordinate U 2 →ₐ[R] P :=
  (scaleOneSlopeEquiv U 1 0 0 0 rfl rfl rfl rfl rfl).toAlgHom.comp
    (fromOriginal U 1 0 0 0 (by simp [splitNodalEquation])
      (by simp [splitNodalEquation]) (by simp [splitNodalEquation]))

/-- The horizontal cubic coordinate of the split input is the two tangent factors. -/
theorem splitSlopeAffineInput_x : splitSlopeAffineInput a (coord U 2 0) = z * (z + A) := by
  unfold splitSlopeAffineInput
  erw [AlgHom.comp_apply, fromOriginal_x]
  exact scaleOneSlopeEquiv_x U 1 0 0 0 rfl rfl rfl rfl rfl

/-- The vertical cubic coordinate retains the actual slope. -/
theorem splitSlopeAffineInput_y :
    splitSlopeAffineInput a (coord U 2 1) = z * (z + A) * z := by
  unfold splitSlopeAffineInput
  erw [AlgHom.comp_apply, fromOriginal_y]
  exact scaleOneSlopeEquiv_y U 1 0 0 0 rfl rfl rfl rfl rfl

variable (W : WeierstrassCurve R) (r : R)
  (ha : (a : R) = W.a₁ + 2 * r) (hr : r ^ 2 + W.a₁ * r - W.a₂ = 0)
  (h3 : W.a₃ = 0) (h4 : W.a₄ = 0) (h6 : W.a₆ = 0)
local notation "C" => (VariableChange.mk 1 0 r 0 : VariableChange R)
local notation "he" => rootShearCurve_eq_splitNodal W r a ha hr h3 h4 h6
local notation "E" => integralVariableChangeIso W U C he
local notation "I" => rootShearTorusSmoothIso W r a ha hr h3 h4 h6

/-- The original affine coordinates determine the full root-shear algebra map. -/
theorem rootShearSlopeInput_algebra
    (f : Coordinate W 2 →ₐ[R] P)
    (hx : f (coord W 2 0) = z * (z + A))
    (hy : f (coord W 2 1) = z * (z + A) * (z + algebraMap R P r)) :
    f = (splitSlopeAffineInput a).comp (affineVariableChangeMap W U C he) := by
  apply hom_ext
  intro i
  fin_cases i
  · change f (coord W 2 0) =
      (splitSlopeAffineInput a) (affineVariableChangeMap W U C he (coord W 2 0))
    simpa only [ affineVariableChangeMap_x, Units.val_one,
      map_one, one_pow, one_mul, map_zero, add_zero, splitSlopeAffineInput_x] using hx
  · change f (coord W 2 1) =
      (splitSlopeAffineInput a) (affineVariableChangeMap W U C he (coord W 2 1))
    simp only [affineVariableChangeMap_y, Units.val_one,
      map_one, one_pow, one_mul, map_zero, add_zero, map_add, map_mul,
      AlgHom.commutes, splitSlopeAffineInput_x, splitSlopeAffineInput_y, hy]
    ring
  · simp only [show (⟨2, by decide⟩ : Fin 3) = 2 from rfl, coord_self, map_one]

/-- The original slope input is the actual torus map into the original smooth cubic. -/
theorem rootShearSlopeInput_toCurve
    (f : Coordinate W 2 →ₐ[R] P)
    (hx : f (coord W 2 0) = z * (z + A))
    (hy : f (coord W 2 1) = z * (z + A) * (z + algebraMap R P r)) :
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫ integralCurveChart W 2 =
      Spec.map (CommRingCat.ofHom (slopeLaurentMap a).toRingHom) ≫
        (I).hom ≫ (integralSmoothOpen W).ι := by
  rw [rootShearTorusSmoothIso_inclusion]
  rw [← Category.assoc, ← slopeLaurentMap_toCurve a (splitSlopeAffineInput a)
    (splitSlopeAffineInput_x a) (splitSlopeAffineInput_y a)]
  rw [Category.assoc, integralVariableChangeIso_affine]
  change _ = Spec.map _ ≫ Spec.map _ ≫ integralCurveChart W 2
  rw [← Spec.map_comp_assoc]
  rw [rootShearSlopeInput_algebra a W r ha hr h3 h4 h6 f hx hy]
  rfl

end FLT.Mazur.WeierstrassIntegralChart
