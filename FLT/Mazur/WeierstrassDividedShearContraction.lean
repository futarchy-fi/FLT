/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationShear
public import FLT.Mazur.WeierstrassModificationXShear
public import FLT.Mazur.WeierstrassVariableChangeAffineRestriction

/-!
# The chart shears preserve the actual original cubic contraction

Both chart isomorphisms lie over the original integral variable change.
All original affine coordinates are checked, including the exceptional chart.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] {W : WeierstrassCurve R} {π : R}
  {k : ℕ} (d : Data W π k) (r : R)
local notation "U" => rootShearCurve W r
local notation "e" => shearData d r
local notation "C₀" => WeierstrassCurve.VariableChange.mk (1 : Rˣ) 0 r 0
local notation "φ" => affineVariableChangeMap W U C₀ rfl
local notation "F" => WeierstrassDilatation.fromOriginal W (π ^ k)
  d.b3 d.b4 d.b6 d.factor3 d.factor4 d.factor6
local notation "G" => WeierstrassDilatation.fromOriginal U (π ^ k)
  d.b3 (d.b4 - r * d.b3) d.b6
  (Data.factor3 e) (Data.factor4 e) (Data.factor6 e)

/-- All original affine functions commute with the divided-chart shear. -/
theorem shearChart_fromOriginal :
    (WeierstrassDilatation.shearForward W (π ^ k) d.b3 d.b4 d.b6 r).comp F =
      (G).comp φ := by
  apply WeierstrassIntegralChart.hom_ext
  intro i
  fin_cases i
  · change WeierstrassDilatation.shearForward W (π ^ k) d.b3 d.b4 d.b6 r
      (F (coord W 2 0)) = G (φ (coord W 2 0))
    simp only [WeierstrassDilatation.fromOriginal_x,
      map_mul, AlgHom.commutes, WeierstrassDilatation.shearForward_x,
      affineVariableChangeMap_x, Units.val_one, map_one, one_pow, one_mul, map_zero,
      add_zero]
  · change WeierstrassDilatation.shearForward W (π ^ k) d.b3 d.b4 d.b6 r
      (F (coord W 2 1)) = G (φ (coord W 2 1))
    simp only [WeierstrassDilatation.fromOriginal_y,
      map_mul, AlgHom.commutes, WeierstrassDilatation.shearForward_y,
      affineVariableChangeMap_y, Units.val_one, map_one, one_pow, one_mul, map_zero,
      add_zero]
    rw [map_add, map_mul, AlgHom.commutes, WeierstrassDilatation.fromOriginal_x,
      WeierstrassDilatation.fromOriginal_y]
    ring
  · have hi : (⟨2, by decide⟩ : Fin 3) = 2 := rfl
    simp only [hi, coord_self, map_one]

/-- The full divided-chart scheme isomorphism, contravariant to the explicit algebra shear. -/
def shearChartIso : chart (shearData d r) ≅ chart d :=
  Scheme.Spec.mapIso (WeierstrassDilatation.shearEquiv W (π ^ k) d.b3 d.b4 d.b6 r
    ).toRingEquiv.toCommRingCatIso.op

/-- The divided-chart isomorphism retains its original integral cubic map. -/
@[reassoc] theorem shearChartIso_toCurve :
    (shearChartIso d r).hom ≫ toCurve d =
      toCurve (shearData d r) ≫ (integralVariableChangeIso W U C₀ rfl).hom := by
  change Spec.map _ ≫ (Spec.map _ ≫ integralCurveChart W 2) =
    (Spec.map _ ≫ integralCurveChart U 2) ≫ _
  rw [Category.assoc, integralVariableChangeIso_affine]
  change Spec.map _ ≫ Spec.map _ ≫ integralCurveChart W 2 =
    Spec.map _ ≫ Spec.map _ ≫ integralCurveChart W 2
  simp only [← Spec.map_comp_assoc]
  have he := congrArg (fun f : Coordinate W 2 →ₐ[R]
      WeierstrassDilatation.Coordinate U (π ^ k) d.b3 (d.b4 - r * d.b3) d.b6 =>
        Spec.map (CommRingCat.ofHom f.toRingHom) ≫ integralCurveChart W 2)
    (shearChart_fromOriginal d r)
  exact he

local notation "H" => WeierstrassModificationX.fromOriginal W (π ^ k)
  d.b3 d.b4 d.b6 d.factor3 d.factor4 d.factor6
local notation "J" => WeierstrassModificationX.fromOriginal U (π ^ k)
  d.b3 (d.b4 - r * d.b3) d.b6
  (Data.factor3 e) (Data.factor4 e) (Data.factor6 e)

/-- All original affine functions commute on the complete incidence chart. -/
theorem shearIncidence_fromOriginal :
    (WeierstrassModificationX.shearForward W (π ^ k) d.b3 d.b4 d.b6 r).comp H =
      (J).comp φ := by
  apply WeierstrassIntegralChart.hom_ext
  intro i
  fin_cases i
  · change WeierstrassModificationX.shearForward W (π ^ k) d.b3 d.b4 d.b6 r
      (H (coord W 2 0)) = J (φ (coord W 2 0))
    simp only [WeierstrassModificationX.fromOriginal_x,
      WeierstrassModificationX.shearForward_x, affineVariableChangeMap_x, Units.val_one,
      map_one, one_pow, one_mul, map_zero, add_zero]
  · change WeierstrassModificationX.shearForward W (π ^ k) d.b3 d.b4 d.b6 r
      (H (coord W 2 1)) = J (φ (coord W 2 1))
    simp only [WeierstrassModificationX.fromOriginal_y,
      WeierstrassModificationX.shearForward_y, affineVariableChangeMap_y, Units.val_one,
      map_one, one_pow, one_mul, map_zero, add_zero]
    rw [map_add, map_mul, AlgHom.commutes, WeierstrassModificationX.fromOriginal_x,
      WeierstrassModificationX.fromOriginal_y]
  · have hi : (⟨2, by decide⟩ : Fin 3) = 2 := rfl
    simp only [hi, coord_self, map_one]

/-- The actual complete incidence chart is identified under the shear. -/
def shearIncidenceIso :
    Spec (.of (WeierstrassModificationX.Coordinate U (π ^ k) d.b3 (d.b4 - r * d.b3) d.b6)) ≅
      Spec (.of (WeierstrassModificationX.Coordinate W (π ^ k) d.b3 d.b4 d.b6)) :=
  Scheme.Spec.mapIso (WeierstrassModificationX.shearEquiv W (π ^ k) d.b3 d.b4 d.b6 r
    ).toRingEquiv.toCommRingCatIso.op

/-- The full incidence chart, including its exceptional conic, retains the cubic projection. -/
@[reassoc] theorem shearIncidenceIso_toCurve :
    (shearIncidenceIso d r).hom ≫
        WeierstrassModificationX.toCurve W (π ^ k) d.b3 d.b4 d.b6
          d.factor3 d.factor4 d.factor6 =
      WeierstrassModificationX.toCurve U (π ^ k) d.b3 (d.b4 - r * d.b3) d.b6
        (Data.factor3 e) (Data.factor4 e) (Data.factor6 e) ≫
        (integralVariableChangeIso W U C₀ rfl).hom := by
  change Spec.map _ ≫ (Spec.map _ ≫ integralCurveChart W 2) =
    (Spec.map _ ≫ integralCurveChart U 2) ≫ _
  rw [Category.assoc, integralVariableChangeIso_affine]
  change Spec.map _ ≫ Spec.map _ ≫ integralCurveChart W 2 =
    Spec.map _ ≫ Spec.map _ ≫ integralCurveChart W 2
  simp only [← Spec.map_comp_assoc]
  have he := congrArg (fun f : Coordinate W 2 →ₐ[R]
      WeierstrassModificationX.Coordinate U (π ^ k) d.b3 (d.b4 - r * d.b3) d.b6 =>
        Spec.map (CommRingCat.ofHom f.toRingHom) ≫ integralCurveChart W 2)
    (shearIncidence_fromOriginal d r)
  exact he

end FLT.Mazur.WeierstrassDividedDepth
