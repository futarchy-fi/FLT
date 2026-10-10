/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassNodalResidueCharts
public import FLT.Mazur.WeierstrassDividedTensorYBoundary
public import FLT.Mazur.WeierstrassIntegralProductOverlap

/-!
# The original Y/Z transition in full nodal coordinates

The tensor normalization preserves the inverse normalizing coordinate and
hence the entire original transition, including its coefficient structure.
-/

@[expose] public noncomputable section
open IsLocalRing AlgebraicGeometry CategoryTheory Limits
open scoped TensorProduct
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {depth : ℕ} (D : SplitNodeDepth W π depth)
  (hdepth : 0 < depth)
local notation "K" => ResidueField R
local notation "N" => splitNodalEquation (WeierstrassDilatation.residueTangentUnit D)

/-- The original chart functions mapped into their nodal residue chart. -/
def nodalResidueChartMap (j : Fin 3) : Coordinate W j →ₐ[R] Coordinate N j :=
  ((nodalResidueChartEquiv D hdepth j).toAlgHom.restrictScalars R).comp
    Algebra.TensorProduct.includeRight

/-- Original chart coordinates retain their exact nodal values. -/
theorem nodalResidueChartMap_coord (j i : Fin 3) :
    nodalResidueChartMap D hdepth j (coord W j i) = coord N j i :=
  nodalResidueChartEquiv_coord D hdepth j i

/-- The original overlap functions mapped into the full nodal residue overlap. -/
def nodalResidueOverlapMap (j k : Fin 3) : Overlap W j k →ₐ[R] Overlap N j k :=
  ((nodalResidueBoundaryEquiv D hdepth j k).toAlgHom.restrictScalars R).comp
    Algebra.TensorProduct.includeRight

/-- The original localized coordinates are unchanged by nodal normalization. -/
theorem nodalResidueOverlapMap_coord (j k i : Fin 3) :
    nodalResidueOverlapMap D hdepth j k (overlapCoord W j k i) = overlapCoord N j k i :=
  nodalResidueBoundaryEquiv_coord D hdepth j k i

/-- The entire original inverse normalizing coordinate survives in the nodal overlap. -/
theorem nodalResidueOverlapMap_inverse (j k : Fin 3) :
    nodalResidueOverlapMap D hdepth j k (overlapInverse W j k) = overlapInverse N j k := by
  apply (overlapCoord_isUnit N j k).mul_right_cancel
  rw [← nodalResidueOverlapMap_coord D hdepth j k k, ← map_mul,
    overlapInverse_mul, map_one, nodalResidueOverlapMap_coord, overlapInverse_mul]

/-- Every original transition function agrees with the corresponding nodal function. -/
theorem nodalResidueOverlapMap_transitionBase (j k : Fin 3) :
    (nodalResidueOverlapMap D hdepth j k).comp (transitionBase W j k) =
      ((transitionBase N j k).restrictScalars R).comp (nodalResidueChartMap D hdepth k) := by
  apply hom_ext
  intro i
  change nodalResidueOverlapMap D hdepth j k (transitionBase W j k (coord W k i)) =
    transitionBase N j k (nodalResidueChartMap D hdepth k (coord W k i))
  rw [transitionBase_coord, map_mul, nodalResidueOverlapMap_inverse,
    nodalResidueOverlapMap_coord, nodalResidueChartMap_coord, transitionBase_coord]

/-- Nodal chart normalization preserves its actual residue coefficient structure. -/
@[reassoc] theorem nodalResidueChartIso_structure (j : Fin 3) :
    (nodalResidueChartIso D hdepth j).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap K (K ⊗[R] Coordinate W j))) =
        chartStructure N j := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext (nodalResidueChartEquiv D hdepth j).commutes)

/-- The nodal Y/Z transition retains every original integral infinity-chart function. -/
@[reassoc] theorem nodalResidueBoundaryIso_infinity_projection :
    (nodalResidueBoundaryIso D hdepth 2 1).hom ≫
      TensorOpenChart.projection ≫ affineBoundaryToY W =
        affineBoundaryToY N ≫ (nodalResidueChartIso D hdepth 1).hom ≫
          TensorOpenChart.projection := by
  rw [affineBoundaryToY, ← chartOverlapOther_transition,
    affineBoundaryToY, ← chartOverlapOther_transition]
  change Spec.map _ ≫ Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp_assoc, ← Spec.map_comp, ← Spec.map_comp_assoc, ← Spec.map_comp]
  congr 1
  exact congrArg (fun f : Coordinate W 1 →ₐ[R] Overlap N 2 1 =>
    CommRingCat.ofHom f.toRingHom) (nodalResidueOverlapMap_transitionBase D hdepth 2 1)

/-- The whole original tensor boundary transition is the actual nodal Y/Z transition. -/
@[reassoc] theorem nodalResidueBoundaryIso_infinity :
    (nodalResidueBoundaryIso D hdepth 2 1).hom ≫
      WeierstrassDividedDepth.tensorBoundaryToInfinity (W := W) K =
        affineBoundaryToY N ≫ (nodalResidueChartIso D hdepth 1).hom := by
  apply (cancel_mono (pullbackSpecIso R K (Coordinate W 1)).inv).mp
  apply pullback.hom_ext
  · simp only [Category.assoc]
    rw [pullbackSpecIso_inv_fst',
      WeierstrassDividedDepth.tensorBoundaryToInfinity_structure,
      nodalResidueBoundaryIso_structure, nodalResidueChartIso_structure,
      WeierstrassDividedDepth.affineBoundaryToY_structure]
  · simp only [Category.assoc]
    rw [pullbackSpecIso_inv_snd]
    change (nodalResidueBoundaryIso D hdepth 2 1).hom ≫
      WeierstrassDividedDepth.tensorBoundaryToInfinity (W := W) K ≫
        TensorOpenChart.projection = _
    rw [WeierstrassDividedDepth.tensorBoundaryToInfinity_projection,
      nodalResidueBoundaryIso_infinity_projection]
    rfl

end FLT.Mazur.WeierstrassIntegralChart
