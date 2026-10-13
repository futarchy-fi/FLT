/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicLegendreSwapLift
/-! # The global cyclic swap is an involution

The actual swap on the quadratic root cover commutes with the covering
projection and the descended parameter-changing swap. Canceling the
epimorphic covering projection transfers the local square identity to
the global cyclic automorphism.

This proves the swap relation only. The reciprocal and mixed relations,
the modular quotient, and the arithmetic input to Mazur remain separate.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace WeierstrassCurve.CubicCharts

theorem legendreSwapDescendedIso_inv (p : ℕ) [Fact p.Prime] :
    (legendreSwapDescendedIso p).inv.left = legendreSwapReturnDescendedMap p := by
  apply (cancel_mono (legendreSwapDescendedIso p).hom.left).mp
  have hi := congrArg Over.Hom.left (legendreSwapDescendedIso p).inv_hom_id
  change _ ≫ _ = 𝟙 _ at hi
  rw [hi]
  exact (legendreSwapReturnDescendedMap_comp p).symm

theorem legendreSwapCyclicAut_hom (p : ℕ) [Fact p.Prime] :
    (legendreSwapCyclicAut p).hom =
      legendreSwapReturnDescendedMap p ≫
        (cyclicModelCongr _ p _ (legendreSwap_model_map p)).inv.left ≫
          ringHomCyclicMap (legendreModel p) p (legendreSwapParameterEquiv p).toRingHom := by
  change ((legendreSwapDescendedIso p).inv.left ≫
    (cyclicModelCongr _ p _ (legendreSwap_model_map p)).inv.left) ≫
      (ringEquivCyclicIso _ p _).hom = _
  rw [legendreSwapDescendedIso_inv, ringEquivCyclicIso_ringHom, Category.assoc]

theorem legendreSwapRootMap_base (p : ℕ) :
    (legendreSwapRootMap p).comp
        (algebraMap (LegendreBase p) (LegendreUniversalSwapRing p)) =
      (algebraMap (LegendreBase p) (LegendreUniversalSwapRing p)).comp
        (legendreSwapParameterEquiv p).toRingHom := by
  ext x
  exact legendreSwapRootMap_scalar p x

attribute [local irreducible] variableChangeCongrOverIso groupCyclicParameterIso

theorem legendreSwapReturn_fac (p : ℕ) [Fact p.Prime] :
    ringHomCyclicMap (legendreModel p) p
        (algebraMap (LegendreBase p) (LegendreUniversalSwapRing p)) ≫
      legendreSwapReturnDescendedMap p =
    (groupCyclicParameterIso p (variableChangeCongrOverIso
      ((legendreCurve (1 - legendreParameter p)).map
        (algebraMap (LegendreBase p) (LegendreUniversalSwapRing p)))
      (legendreSwapCoverModel p)
      (signCoordinateChange (quadraticEtaleUnit (-1 : (LegendreBase p)ˣ))
        (algebraMap (LegendreBase p) (LegendreUniversalSwapRing p) 1))
      (legendreSwap_return_coordinate_equation p))).hom.left ≫
        ringHomCyclicMap (legendreCurve (1 - legendreParameter p)) p
          (algebraMap (LegendreBase p) (LegendreUniversalSwapRing p)) := by
  simp only [ringHomCyclicMap_algebraMap, legendreSwapReturnDescendedMap]
  exact quadraticCoordinateDesc_fac (legendreCurve (1 - legendreParameter p)) p
    (-1 : (LegendreBase p)ˣ) (legendreModel p) rfl rfl 1
    (legendreSwap_return_coordinate_equation p)


theorem legendreSwapCoverCyclicMap_comparison (p : ℕ) [Fact p.Prime] :
    legendreSwapCoverCyclicMap p ≫
        ringHomCyclicMap (legendreModel p) p
          (algebraMap (LegendreBase p) (LegendreUniversalSwapRing p)) =
      ringHomCyclicMap (legendreModel p) p
          (algebraMap (LegendreBase p) (LegendreUniversalSwapRing p)) ≫
        (legendreSwapCyclicAut p).hom := by
  rw [legendreSwapCyclicAut_hom,
    ← Category.assoc _ (legendreSwapReturnDescendedMap p), legendreSwapReturn_fac,
    cyclicModelCongr_inv]
  simp only [Category.assoc]
  rw [← Category.assoc (ringHomCyclicMap
    (legendreCurve (1 - legendreParameter p)) p
      (algebraMap (LegendreBase p) (LegendreUniversalSwapRing p))),
    ringHomCyclicMap_curve_congr]
  simp only [← Category.assoc]
  rw [variableChangeCyclic_source_congr]
  simp only [Category.assoc]
  rw [ringHomCyclicMap_comp, ← Category.assoc, variableChangeCyclic_source_congr]
  unfold legendreSwapCoverCyclicMap
  rw [Category.assoc, ringHomCyclicMap_comp_eq _ _
    (algebraMap (LegendreBase p) (LegendreUniversalSwapRing p))
    (legendreSwapRootMap p)
    ((algebraMap (LegendreBase p) (LegendreUniversalSwapRing p)).comp
      (legendreSwapParameterEquiv p).toRingHom)
    (legendreSwapRootMap_base p),
    ← Category.assoc, variableChangeCyclic_source_congr]
  simp only [map_one, signCoordinateChange, legendreSwapChange]


theorem legendreSwapCyclicAut_square (p : ℕ) [Fact p.Prime] :
    (legendreSwapCyclicAut p).hom ≫ (legendreSwapCyclicAut p).hom = 𝟙 _ := by
  let q := ringHomCyclicMap (legendreModel p) p
    (algebraMap (LegendreBase p) (LegendreUniversalSwapRing p))
  have : Epi q := by
    dsimp [q]
    rw [ringHomCyclicMap_algebraMap]
    infer_instance
  apply (cancel_epi q).mp
  dsimp [q]
  rw [← Category.assoc, ← legendreSwapCoverCyclicMap_comparison, Category.assoc,
    ← legendreSwapCoverCyclicMap_comparison, ← Category.assoc,
    legendreSwapCoverCyclicMap_square, Category.id_comp, Category.comp_id]

end WeierstrassCurve.CubicCharts
