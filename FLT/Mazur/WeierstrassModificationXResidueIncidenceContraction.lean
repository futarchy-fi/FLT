/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXResidueContractionGeometry
public import FLT.Mazur.WeierstrassModificationXResidueTensorFunctions

/-!
# The actual incidence open contracts to the original residue node

Invert the image of the original tensor t, without identifying it with a
renamed normal-form generator. The original contraction becomes the constant
point [0:0:1] of the same cubic. The proof retains the middle-depth coefficient.
-/

@[expose] public noncomputable section

open IsLocalRing AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassModificationX

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {n : ℕ} (D : SplitNodeDepth W π n)
  (k : ℕ) (hk0 : 0 < k) (hk : 2 * k ≤ n) (b3 b4 b6 : R)
  (h3 : W.a₃ = π ^ k * b3) (h4 : W.a₄ = π ^ k * b4)
  (h6 : W.a₆ = (π ^ k) ^ 2 * b6)

local notation "K" => ResidueField R
local notation "F" => FiberCoordinate (residue R W.a₁) (residue R b6)
local notation "f" => residueNormalMap D k hk0 hk b3 b4 b6 h3 h4
local notation "O" => Localization.Away (f (t W (π ^ k) b3 b4 b6))

omit [IsDomain R] in
include D hk0 h6 in
/-- The original cubic contains the residue point at the origin. -/
theorem residueOrigin_equation :
    (W.map (algebraMap R K)).toProjective.Equation ![0, 0, 1] := by
  have hs : algebraMap R K (π ^ k) = 0 :=
    WeierstrassDilatation.residue_scale_eq_zero D k hk0
  have hzero : algebraMap R K W.a₆ = 0 := by
    rw [h6, map_mul, map_pow, hs, zero_pow (by decide : 2 ≠ 0), zero_mul]
  simpa only [WeierstrassCurve.Projective.equation_iff,
    WeierstrassCurve.Projective.fin3_def_ext, WeierstrassCurve.map_a₆,
    zero_pow (by decide : 2 ≠ 0), zero_pow (by decide : 3 ≠ 0), one_pow,
    zero_mul, mul_zero, add_zero, zero_add, mul_one, sub_eq_zero] using hzero.symm

/-- Evaluation at the original residue node of the same projective cubic. -/
def residueOriginMap : WeierstrassIntegralChart.Coordinate W 2 →ₐ[R] K :=
  WeierstrassIntegralChart.evaluation W 2 ![0, 0, 1]
    (residueOrigin_equation D k hk0 b6 h6) rfl

omit [IsDomain R] in
/-- The origin map keeps all three normalized projective coordinates explicit. -/
@[simp] theorem residueOriginMap_coord (i : Fin 3) :
    residueOriginMap D k hk0 b6 h6 (WeierstrassIntegralChart.coord W 2 i) =
      ![0, 0, 1] i := WeierstrassIntegralChart.evaluation_coord _ _ _ _ _ _

/-- On the actual tensor-incidence open the original x function is zero. -/
theorem residueIncidenceOpen_x :
    algebraMap F O (f (x W (π ^ k) b3 b4 b6)) = 0 := by
  apply (IsLocalization.Away.algebraMap_isUnit (f (t W (π ^ k) b3 b4 b6))).mul_left_cancel
  rw [mul_zero, ← map_mul, residueNormalMap_incidence, map_zero]

/-- The original y function is also zero on that same actual open. -/
theorem residueIncidenceOpen_y :
    algebraMap F O (f (y W (π ^ k) b3 b4 b6)) = 0 := by
  rw [residueNormalMap_y, map_mul, residueIncidenceOpen_x, zero_mul]

/-- The affine contraction on the actual tensor-incidence open factors through the residue node. -/
theorem residueIncidenceOpen_coordinateMap :
    (IsScalarTower.toAlgHom R F O).comp
        (residueOriginalCoordinateMap D k hk0 hk b3 b4 b6 h3 h4 h6) =
      (IsScalarTower.toAlgHom R K O).comp (residueOriginMap D k hk0 b6 h6) := by
  apply WeierstrassIntegralChart.hom_ext
  intro i
  fin_cases i
  · change algebraMap F O ((residueOriginalCoordinateMap D k hk0 hk b3 b4 b6 h3 h4 h6)
      (WeierstrassIntegralChart.coord W 2 0)) =
        algebraMap K O (residueOriginMap D k hk0 b6 h6
          (WeierstrassIntegralChart.coord W 2 0))
    rw [residueOriginalCoordinateMap_x, residueOriginMap_coord]
    change algebraMap F O (f (x W (π ^ k) b3 b4 b6)) = algebraMap K O 0
    rw [map_zero]
    exact residueIncidenceOpen_x D k hk0 hk b3 b4 b6 h3 h4
  · change algebraMap F O ((residueOriginalCoordinateMap D k hk0 hk b3 b4 b6 h3 h4 h6)
      (WeierstrassIntegralChart.coord W 2 1)) =
        algebraMap K O (residueOriginMap D k hk0 b6 h6
          (WeierstrassIntegralChart.coord W 2 1))
    rw [residueOriginalCoordinateMap_y, residueOriginMap_coord]
    change algebraMap F O (f (y W (π ^ k) b3 b4 b6)) = algebraMap K O 0
    rw [map_zero]
    exact residueIncidenceOpen_y D k hk0 hk b3 b4 b6 h3 h4
  · change algebraMap F O ((residueOriginalCoordinateMap D k hk0 hk b3 b4 b6 h3 h4 h6)
      (WeierstrassIntegralChart.coord W 2 2)) =
        algebraMap K O (residueOriginMap D k hk0 b6 h6
          (WeierstrassIntegralChart.coord W 2 2))
    rw [WeierstrassIntegralChart.coord_self, map_one, map_one, map_one, map_one]

/-- The incidence localization is an actual open of the original tensor normal form. -/
def residueIncidenceOpenImmersion : Spec (.of O) ⟶ Spec (.of F) :=
  Spec.map (CommRingCat.ofHom (algebraMap F O))

instance residueIncidenceOpenImmersion_isOpenImmersion :
    IsOpenImmersion (residueIncidenceOpenImmersion D k hk0 hk b3 b4 b6 h3 h4) :=
  IsOpenImmersion.of_isLocalization (f (t W (π ^ k) b3 b4 b6))

/-- The actual open contracts to [0:0:1] on the original cubic, including at middle depth. -/
@[reassoc] theorem residueIncidenceOpen_contraction :
    residueIncidenceOpenImmersion D k hk0 hk b3 b4 b6 h3 h4 ≫
        residueFullContraction D k hk0 hk b3 b4 b6 h3 h4 h6 =
      Spec.map (CommRingCat.ofHom (algebraMap K O)) ≫
        Spec.map (CommRingCat.ofHom (residueOriginMap D k hk0 b6 h6).toRingHom) ≫
          WeierstrassIntegralChart.integralCurveChart W 2 := by
  change Spec.map _ ≫ (Spec.map _ ≫ _) = Spec.map _ ≫ (Spec.map _ ≫ _)
  simp only [← Category.assoc, ← Spec.map_comp]
  congr 2
  exact congrArg (fun g => CommRingCat.ofHom g.toRingHom)
    (residueIncidenceOpen_coordinateMap D k hk0 hk b3 b4 b6 h3 h4 h6)

end FLT.Mazur.WeierstrassModificationX
