/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationZeroResidue
public import FLT.Mazur.TensorOpenChart

/-!
# The full depth-zero divided chart with its original cubic contraction

The actual tensor chart is the nodal affine cubic, with both original
coordinates and its coefficient structure. Its comparison commutes with
the original contraction on every function, not merely on points.
-/

@[expose] public noncomputable section
open IsLocalRing AlgebraicGeometry CategoryTheory
open scoped TensorProduct
namespace FLT.Mazur.WeierstrassDilatation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {depth : ℕ} (D : SplitNodeDepth W π depth)
  (hdepth : 0 < depth) (k : ℕ) (hk : k = 0) (b3 b4 b6 : R)
  (h3 : W.a₃ = π ^ k * b3) (h4 : W.a₄ = π ^ k * b4)
  (h6 : W.a₆ = (π ^ k) ^ 2 * b6)
local notation "K" => ResidueField R
local notation "N" => WeierstrassIntegralChart.splitNodalEquation (residueTangentUnit D)
local notation "A" => WeierstrassIntegralChart.Coordinate N 2
local notation "e" => zeroResidueNodalEquiv D hdepth k hk b3 b4 b6 h3 h4 h6
local notation "T" => ScalarExtension W (π ^ k) b3 b4 b6 K

/-- The original affine functions reduced to the actual nodal equation. -/
def zeroResidueOriginalMap : WeierstrassIntegralChart.Coordinate W 2 →ₐ[R] A :=
  ((WeierstrassIntegralChart.equationChartEquiv
    (WeierstrassIntegralChart.splitDepth_residue_equation D hdepth) 2).toAlgHom.restrictScalars
      R).comp
      (WeierstrassIntegralChart.chartCoefficientMap W 2)

/-- The original normalized coordinates reduce to exactly the nodal cubic coordinates. -/
theorem zeroResidueOriginalMap_coord (i : Fin 3) :
    zeroResidueOriginalMap D hdepth (WeierstrassIntegralChart.coord W 2 i) =
      WeierstrassIntegralChart.coord N 2 i := by
  rw [zeroResidueOriginalMap, AlgHom.comp_apply,
    WeierstrassIntegralChart.chartCoefficientMap_coord]
  exact WeierstrassIntegralChart.equationChartEquiv_coord _ 2 i

/-- The full tensor normalization retains the original affine contraction on every function. -/
theorem zeroResidueNodalEquiv_original :
    (((e).toAlgHom.restrictScalars R).comp Algebra.TensorProduct.includeRight).comp
      (fromOriginal W (π ^ k) b3 b4 b6 h3 h4 h6) = zeroResidueOriginalMap D hdepth := by
  apply WeierstrassIntegralChart.hom_ext
  intro i
  have hs : algebraMap R (Coordinate W (π ^ k) b3 b4 b6) (π ^ k) = 1 := by
    simp only [hk, pow_zero, map_one]
  rw [zeroResidueOriginalMap_coord]
  fin_cases i
  · have hx : fromOriginal W (π ^ k) b3 b4 b6 h3 h4 h6
        (WeierstrassIntegralChart.coord W 2 0) = x W (π ^ k) b3 b4 b6 := by
      rw [fromOriginal_x, hs, one_mul]
    exact (congrArg (fun z : Coordinate W (π ^ k) b3 b4 b6 =>
      (e) (Algebra.TensorProduct.includeRight z)) hx).trans
        (zeroResidueNodalEquiv_x D hdepth k hk b3 b4 b6 h3 h4 h6)
  · have hy : fromOriginal W (π ^ k) b3 b4 b6 h3 h4 h6
        (WeierstrassIntegralChart.coord W 2 1) = y W (π ^ k) b3 b4 b6 := by
      rw [fromOriginal_y, hs, one_mul]
    exact (congrArg (fun z : Coordinate W (π ^ k) b3 b4 b6 =>
      (e) (Algebra.TensorProduct.includeRight z)) hy).trans
        (zeroResidueNodalEquiv_y D hdepth k hk b3 b4 b6 h3 h4 h6)
  · change ((((e).toAlgHom.restrictScalars R).comp
      Algebra.TensorProduct.includeRight).comp
        (fromOriginal W (π ^ k) b3 b4 b6 h3 h4 h6))
          (WeierstrassIntegralChart.coord W 2 2) = WeierstrassIntegralChart.coord N 2 2
    rw [WeierstrassIntegralChart.coord_self, WeierstrassIntegralChart.coord_self, map_one]

/-- The nodal affine spectrum identifies the whole actual zero-depth tensor chart. -/
def zeroResidueNodalIso : Spec (.of A) ≅ Spec (.of T) :=
  Scheme.Spec.mapIso (e).toRingEquiv.toCommRingCatIso.op

/-- The whole nodal comparison preserves the actual residue coefficient structure. -/
@[reassoc] theorem zeroResidueNodalIso_structure :
    (zeroResidueNodalIso D hdepth k hk b3 b4 b6 h3 h4 h6).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap K T)) =
        Spec.map (CommRingCat.ofHom (algebraMap K A)) := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext (e).commutes)

/-- The full original projective contraction of the normalized depth-zero chart. -/
def zeroResidueNodalContraction : Spec (.of A) ⟶ WeierstrassIntegralChart.integralCurve W :=
  Spec.map (CommRingCat.ofHom (zeroResidueOriginalMap D hdepth).toRingHom) ≫
    WeierstrassIntegralChart.integralCurveChart W 2

/-- Every original cubic function survives the whole nodal normalization. -/
@[reassoc] theorem zeroResidueNodalIso_contraction :
    (zeroResidueNodalIso D hdepth k hk b3 b4 b6 h3 h4 h6).hom ≫
      TensorOpenChart.projection ≫ toCurve W (π ^ k) b3 b4 b6 h3 h4 h6 =
        zeroResidueNodalContraction D hdepth := by
  change Spec.map _ ≫ Spec.map _ ≫ Spec.map _ ≫ _ = Spec.map _ ≫ _
  rw [← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
  congr 2
  exact congrArg (fun f : WeierstrassIntegralChart.Coordinate W 2 →ₐ[R] A =>
    CommRingCat.ofHom f.toRingHom) (zeroResidueNodalEquiv_original D hdepth k hk b3 b4 b6 h3 h4 h6)

end FLT.Mazur.WeierstrassDilatation
