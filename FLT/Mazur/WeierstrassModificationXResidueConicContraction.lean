/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXConicGeometry
public import FLT.Mazur.WeierstrassModificationXFiberConicGeometry
public import FLT.Mazur.WeierstrassModificationXResidueIncidenceContraction
public import FLT.Mazur.WeierstrassModificationXResidueNamedGenerators

/-!
# The original residue conic and its original cubic contraction

The actual conic component is smooth and embeds into the original tensor
fiber through residueFiberIso. The original x/y functions vanish on the
entire conic, so its original contraction factors through the residue node.
The middle-depth coefficient is retained throughout.
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
local notation "a" => residue R W.a₁
local notation "c" => residue R b6
local notation "F" => FiberCoordinate a c
local notation "C₀" => ConicCoordinate a c
local notation "T" => ScalarExtension W (π ^ k) b3 b4 b6 K
local notation "f" => residueNormalMap D k hk0 hk b3 b4 b6 h3 h4

omit [IsDomain R] in
include D in
/-- The actual residue conic is smooth over the original residue field. -/
theorem residueConic_smooth : Smooth (conicStructure a c) :=
  conicStructure_smooth a c (residue_tangent_isUnit D)

/-- The original horizontal contraction function vanishes on the full conic. -/
theorem residueConic_x : fiberConicMap a c (f (x W (π ^ k) b3 b4 b6)) = 0 := by
  rw [residueNormalMap_x, residueNormalMap_v, residueNormalMap_t,
    IsScalarTower.algebraMap_apply R K F, IsScalarTower.algebraMap_apply R K F]
  change fiberConicMap a c (fiberConicFactor a c) = 0
  exact fiberConicMap_factor a c

/-- The original vertical contraction function also vanishes on the full conic. -/
theorem residueConic_y : fiberConicMap a c (f (y W (π ^ k) b3 b4 b6)) = 0 := by
  rw [residueNormalMap_y, map_mul, residueConic_x, zero_mul]

/-- The original cubic coordinate map on the conic is the original residue node. -/
theorem residueConic_coordinateMap :
    ((fiberConicMap a c).restrictScalars R).comp
        (residueOriginalCoordinateMap D k hk0 hk b3 b4 b6 h3 h4 h6) =
      (IsScalarTower.toAlgHom R K C₀).comp (residueOriginMap D k hk0 b6 h6) := by
  apply WeierstrassIntegralChart.hom_ext
  intro i
  fin_cases i
  · change fiberConicMap a c
      ((residueOriginalCoordinateMap D k hk0 hk b3 b4 b6 h3 h4 h6)
        (WeierstrassIntegralChart.coord W 2 0)) = algebraMap K C₀
          (residueOriginMap D k hk0 b6 h6 (WeierstrassIntegralChart.coord W 2 0))
    rw [residueOriginalCoordinateMap_x, residueOriginMap_coord]
    change _ = algebraMap K C₀ 0
    rw [map_zero]
    exact residueConic_x D k hk0 hk b3 b4 b6 h3 h4
  · change fiberConicMap a c
      ((residueOriginalCoordinateMap D k hk0 hk b3 b4 b6 h3 h4 h6)
        (WeierstrassIntegralChart.coord W 2 1)) = algebraMap K C₀
          (residueOriginMap D k hk0 b6 h6 (WeierstrassIntegralChart.coord W 2 1))
    rw [residueOriginalCoordinateMap_y, residueOriginMap_coord]
    change _ = algebraMap K C₀ 0
    rw [map_zero]
    exact residueConic_y D k hk0 hk b3 b4 b6 h3 h4
  · change fiberConicMap a c
      ((residueOriginalCoordinateMap D k hk0 hk b3 b4 b6 h3 h4 h6)
        (WeierstrassIntegralChart.coord W 2 2)) = algebraMap K C₀
          (residueOriginMap D k hk0 b6 h6 (WeierstrassIntegralChart.coord W 2 2))
    rw [WeierstrassIntegralChart.coord_self, map_one, map_one, map_one, map_one]

/-- The actual conic closed component inside the original tensor fiber. -/
def residueConicImmersion : Spec (.of C₀) ⟶ Spec (.of T) :=
  fiberConicImmersion a c ≫ (residueFiberIso D k hk0 hk b3 b4 b6 h3 h4).hom

instance residueConicImmersion_isClosedImmersion :
    IsClosedImmersion (residueConicImmersion D k hk0 hk b3 b4 b6 h3 h4) :=
  inferInstanceAs (IsClosedImmersion (_ ≫ _))

/-- The conic embedding retains the original full residue contraction. -/
@[reassoc] theorem residueConicImmersion_contraction :
    residueConicImmersion D k hk0 hk b3 b4 b6 h3 h4 ≫
        residueChartContraction k b3 b4 b6 h3 h4 h6 =
      fiberConicImmersion a c ≫ residueFullContraction D k hk0 hk b3 b4 b6 h3 h4 h6 := by
  rw [residueConicImmersion, Category.assoc, residueFiberIso_contraction]

/-- The full original conic contracts to the original node on the original cubic. -/
@[reassoc] theorem residueConic_contraction :
    residueConicImmersion D k hk0 hk b3 b4 b6 h3 h4 ≫
        residueChartContraction k b3 b4 b6 h3 h4 h6 =
      Spec.map (CommRingCat.ofHom (algebraMap K C₀)) ≫
        Spec.map (CommRingCat.ofHom (residueOriginMap D k hk0 b6 h6).toRingHom) ≫
          WeierstrassIntegralChart.integralCurveChart W 2 := by
  rw [residueConicImmersion_contraction]
  change Spec.map _ ≫ (Spec.map _ ≫ _) = Spec.map _ ≫ (Spec.map _ ≫ _)
  simp only [← Category.assoc, ← Spec.map_comp]
  congr 2
  exact congrArg (fun g => CommRingCat.ofHom g.toRingHom)
    (residueConic_coordinateMap D k hk0 hk b3 b4 b6 h3 h4 h6)

end FLT.Mazur.WeierstrassModificationX
