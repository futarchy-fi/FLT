/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonSmoothingZeroFiber
public import FLT.Mazur.PolygonMarkedSections

/-!
# Retaining the original labeled marking on the one-gon

The torus point with coordinate one maps to the actual infinity section of
the cubic. The statement uses the original labeled normalization section.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.OneGonSmoothing
open WeierstrassIntegralChart ProjectiveLineActionSpecialization
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (K : Type*) [Field K]

/-- Evaluation at the original torus identity is infinity evaluation on the cubic chart. -/
theorem torusIdentity_infinityEvaluation :
    (LaurentUnitPoints.evalUnit (R := K) (1 : Kˣ)).comp zeroInfinityToTorus =
      chartInfinityEvaluation (equation (0 : K)) := by
  apply hom_ext
  intro i
  fin_cases i <;> simp [zeroInfinityToTorus, chartInfinityEvaluation]

/-- The original torus identity maps to the actual cubic infinity marking. -/
@[reassoc] theorem unitPoint_zeroTorusInclusion :
    unitPoint K 1 ≫ zeroTorusInclusion K = marking (0 : K) := by
  rw [zeroTorusInclusion, ← Category.assoc]
  change (_ ≫ (zeroTorusChartIso K).hom) ≫ integralCurveChart (equation (0 : K)) 1 =
    Spec.map (CommRingCat.ofHom (chartInfinityEvaluation (equation (0 : K))).toRingHom) ≫ _
  apply congrArg (· ≫ integralCurveChart (equation (0 : K)) 1)
  change Spec.map (CommRingCat.ofHom
    (LaurentUnitPoints.evalUnit (R := K) (1 : Kˣ)).toRingHom) ≫
    Spec.map (CommRingCat.ofHom zeroInfinityToTorus.toRingHom) = _
  rw [← Spec.map_comp]
  exact congrArg (fun f : Coordinate (equation (0 : K)) 1 →ₐ[K] K =>
    Spec.map (CommRingCat.ofHom f.toRingHom)) (torusIdentity_infinityEvaluation K)

/-- Every original label of the single component uses the actual one-gon torus inclusion. -/
theorem original_oneGon_section (a : Kˣ) (i : Fin 1) :
    PolygonMarkedSections.sectionMap K 1 (OneGonNormalization.normalizationOver K) a i =
      unitPoint K a ≫ OneGonGluing.torus K := by
  rw [PolygonMarkedSections.sectionMap, OneGonNormalization.componentι_normalizationOver]
  change unitPoint K a ≫
    ((ProjectiveLine.overlapLeft K ≫ ProjectiveLine.left K) ≫
      OneGonNormalization.normalization K) = _
  rw [OneGonNormalization.torus_normalization]

/-- The global comparison retains the original labeled identity marking. -/
@[reassoc] theorem original_marking_zeroFiberIso (i : Fin 1) :
    PolygonMarkedSections.sectionMap K 1 (OneGonNormalization.normalizationOver K) 1 i ≫
      (zeroFiberIso K).hom = marking (0 : K) := by
  rw [original_oneGon_section, Category.assoc, torus_zeroFiberIso,
    unitPoint_zeroTorusInclusion]

/-- The inverse recovers that same original labeled marking. -/
@[reassoc] theorem marking_zeroFiberIso_inverse (i : Fin 1) :
    marking (0 : K) ≫ (zeroFiberIso K).inv =
      PolygonMarkedSections.sectionMap K 1 (OneGonNormalization.normalizationOver K) 1 i := by
  rw [← original_marking_zeroFiberIso K i, Category.assoc, Iso.hom_inv_id, Category.comp_id]

end FLT.Mazur.OneGonSmoothing
