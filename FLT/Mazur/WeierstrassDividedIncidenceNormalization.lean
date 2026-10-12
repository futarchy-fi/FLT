/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedInitialExteriorProjective

/-!
# The original cubic projection on the complete incidence chart

The split exterior uses the actual original contraction, with x=z(z+a₁)
and y=xz on its entire affine chart, including both node preimages.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart WeierstrassModificationX Polynomial
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j ≤ n)
  (hstart : 0 < start) (hk : 2 * start ≤ depth)
local notation "K" => ResidueField R
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "a" => residue R W.a₁
local notation "c" => residue R (Data.b6 d)
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R K))
local notation "g" => finiteGlobalStructure hπ data j hj

/-- The full original cubic contraction restricted to its actual incidence line. -/
def initialIncidenceNormalization : WeierstrassIntegralChart.Coordinate W 2 →ₐ[R] K[X] :=
  ((fiberIncidenceMap a c).restrictScalars R).comp
    (residueOriginalCoordinateMap D start hstart hk (Data.b3 d) (Data.b4 d) (Data.b6 d)
      (Data.factor3 d) (Data.factor4 d) (Data.factor6 d))

omit [IsBezout R] in
/-- The original x is the product of the two actual tangent factors everywhere. -/
theorem initialIncidenceNormalization_x :
    initialIncidenceNormalization data D hstart hk (coord W 2 0) = X * (X + C a) := by
  change fiberIncidenceMap a c (residueOriginalCoordinateMap D start hstart hk
    (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d)
      (Data.factor6 d) (coord W 2 0)) = _
  rw [residueOriginalCoordinateMap_x, residueNormalMap_x, residueNormalMap_v,
    residueNormalMap_t, IsScalarTower.algebraMap_apply R K (FiberCoordinate a c),
    IsScalarTower.algebraMap_apply R K (FiberCoordinate a c)]
  exact fiberIncidenceMap_factor a c

omit [IsBezout R] in
/-- The original y retains the incidence slope on the entire affine line. -/
theorem initialIncidenceNormalization_y :
    initialIncidenceNormalization data D hstart hk (coord W 2 1) =
      (X * (X + C a)) * X := by
  change fiberIncidenceMap a c (residueOriginalCoordinateMap D start hstart hk
    (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d)
      (Data.factor6 d) (coord W 2 1)) = _
  rw [residueOriginalCoordinateMap_y, residueNormalMap_y, map_mul,
    residueNormalMap_v, fiberIncidenceMap_v]
  have hx := initialIncidenceNormalization_x data D hstart hk
  change fiberIncidenceMap a c (residueOriginalCoordinateMap D start hstart hk
    (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d)
      (Data.factor6 d) (coord W 2 0)) = _ at hx
  rw [residueOriginalCoordinateMap_x] at hx
  exact congrArg (fun t => t * X) hx

omit [IsBezout R] in
/-- The unchanged original x has a regular pullback along the full split normalization. -/
theorem initialIncidenceNormalization_x_regular :
    IsRegular (initialIncidenceNormalization data D hstart hk (coord W 2 0)) := by
  rw [initialIncidenceNormalization_x]
  exact (monic_X.mul (monic_X_add_C a)).isRegular

/-- The actual global incidence map retains every original cubic function. -/
@[reassoc] theorem initialGlobalIncidenceLine_contraction :
    initialGlobalIncidenceLine hπ data D j hj hstart hk ≫ pullback.snd q g ≫
        finiteGlobalContraction hπ data j hj =
      Spec.map (CommRingCat.ofHom
        (initialIncidenceNormalization data D hstart hk).toRingHom) ≫ integralCurveChart W 2 := by
  rw [initialGlobalIncidenceLine, initialGlobalResidueFiberChart]
  simp only [Category.assoc, globalInitialTensorChart_toCurve]
  change fiberIncidenceImmersion a c ≫
    (residueFiberIso D start hstart hk
      (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d)).hom ≫
        residueChartContraction start (Data.b3 d) (Data.b4 d) (Data.b6 d)
          (Data.factor3 d) (Data.factor4 d) (Data.factor6 d) = _
  rw [residueFiberIso_contraction]
  change Spec.map _ ≫ Spec.map _ ≫ _ = _
  rw [← Spec.map_comp_assoc]
  rfl

/-- The complete split exterior has the original normalization on its whole affine chart. -/
@[reassoc] theorem initialProjectiveToGlobal_affine_contraction (hdepth : 0 < depth) :
    ProjectiveLine.left K ≫ initialProjectiveToGlobal hπ data D j hj hstart hk hdepth ≫
        pullback.snd q g ≫ finiteGlobalContraction hπ data j hj =
      Spec.map (CommRingCat.ofHom
        (initialIncidenceNormalization data D hstart hk).toRingHom) ≫ integralCurveChart W 2 := by
  rw [initialProjectiveToGlobal_affine_assoc, initialGlobalIncidenceLine_contraction]

end FLT.Mazur.WeierstrassDividedDepth
