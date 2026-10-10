/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.ProjectiveLineStandardComparison
public import FLT.Mazur.ProjectiveSpaceUniverseReindex
public import FLT.Mazur.ProjectiveUnitChartPoint

/-!
# Homogeneous coordinates for the glued projective line

Lift the two coordinate indices to the coefficient universe. The resulting
Proj comparison realizes arbitrary affine test points in both original charts.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Polynomial
namespace FLT.Mazur.ProjectiveLine
open ProjectiveSpace
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable (K : Type u) [Field K]

/-- The glued line in homogeneous coordinates, including arbitrary coefficient universes. -/
def homogeneousIso : scheme K ≅ space K (ULift.{u} (Fin 2)) :=
  standardIso K ≪≫ UniverseReindex.reindexIso K
    (Equiv.ulift.symm : Fin 2 ≃ ULift.{u} (Fin 2))

/-- Homogeneous coordinates retain the coefficient projection. -/
@[reassoc] theorem homogeneousIso_base :
    (homogeneousIso K).hom ≫ baseProjection K (ULift.{u} (Fin 2)) = toBase K := by
  simp only [homogeneousIso, Iso.trans_hom, Category.assoc]
  exact (congrArg ((standardIso K).hom ≫ ·)
    (UniverseReindex.reindexIso_baseProjection K
      (Equiv.ulift.symm : Fin 2 ≃ ULift.{u} (Fin 2)))).trans (standardIso_toBase K)

/-- The inverse homogeneous comparison retains the coefficient projection. -/
@[reassoc] theorem homogeneousIso_inv_base :
    (homogeneousIso K).inv ≫ toBase K = baseProjection K (ULift.{u} (Fin 2)) := by
  rw [← homogeneousIso_base K, Iso.inv_hom_id_assoc]

variable {S : Type u} [CommRing S] (f : K →+* S) (x : (ULift.{u} (Fin 2)) → S) (b : Sˣ)

/-- A unit zeroth coordinate gives the original left affine coordinate x₁/x₀. -/
@[reassoc] theorem homogeneousPoint_left (h : x (ULift.up 0) = b) :
    unitChartPoint K (ULift.{u} (Fin 2)) f x (ULift.up 0) b h ≫ (homogeneousIso K).inv =
      Spec.map (CommRingCat.ofHom (eval₂RingHom f ((↑b⁻¹ : S) * x (ULift.up 1)))) ≫
        left K := by
  apply (cancel_mono (standardIso K).hom).mp
  simp only [Category.assoc, left_standardIso, homogeneousIso, Iso.trans_inv,
    Iso.inv_hom_id, Category.comp_id]
  rw [unitChartPoint, Category.assoc]
  change Spec.map _ ≫ ProjectiveSpace.chartMap K (ULift.{u} (Fin 2)) (Equiv.ulift.symm 0) ≫
      (UniverseReindex.reindexIso K Equiv.ulift).hom = _
  rw [UniverseReindex.chartMap_reindexIso, ← Category.assoc, ← Spec.map_comp]
  rw [ProjectiveLineStandardCharts.left, ← Category.assoc]
  change Spec.map _ ≫ _ = (Spec.map _ ≫ Spec.map _) ≫ _
  rw [← Spec.map_comp]
  congr 1
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply chartRing_hom_ext
  · intro r
    change unitChartEval K (ULift.{u} (Fin 2)) f x (ULift.up 0) b h
      (UniverseReindex.reindexChartRingMap K Equiv.ulift 0
        (chartScalars K (Fin 2) 0 r)) = _
    have hs : UniverseReindex.reindexChartRingMap K Equiv.ulift 0
        (chartScalars K (Fin 2) 0 r) = chartScalars K (ULift.{u} (Fin 2)) (ULift.up 0) r := by
      apply HomogeneousLocalization.val_injective
      simp [UniverseReindex.reindexChartRingMap, chartScalars, constantsToZero,
        HomogeneousLocalization.fromZeroRingHom, HomogeneousLocalization.map_mk]
    rw [hs, unitChartEval_scalar]
    change _ = eval₂RingHom f _ (ProjectiveLineStandardCharts.leftRingEquiv K _)
    simp
  · intro i
    change unitChartEval K (ULift.{u} (Fin 2)) f x (ULift.up 0) b h
      (UniverseReindex.reindexChartRingMap K Equiv.ulift 0 (coordinate K (Fin 2) 0 i)) = _
    rw [UniverseReindex.reindexChartRingMap_coordinate]
    change unitChartEval K (ULift.{u} (Fin 2)) f x (ULift.up 0) b h
      (coordinate K (ULift.{u} (Fin 2)) (ULift.up 0) (ULift.up i)) = _
    rw [unitChartEval_coordinate]
    change _ = eval₂RingHom f _ (ProjectiveLineStandardCharts.leftRingEquiv K _)
    fin_cases i <;> simp [h]

/-- A unit first coordinate gives the original right affine coordinate x₀/x₁. -/
@[reassoc] theorem homogeneousPoint_right (h : x (ULift.up 1) = b) :
    unitChartPoint K (ULift.{u} (Fin 2)) f x (ULift.up 1) b h ≫ (homogeneousIso K).inv =
      Spec.map (CommRingCat.ofHom (eval₂RingHom f ((↑b⁻¹ : S) * x (ULift.up 0)))) ≫
        right K := by
  apply (cancel_mono (standardIso K).hom).mp
  simp only [Category.assoc, right_standardIso, homogeneousIso, Iso.trans_inv,
    Iso.inv_hom_id, Category.comp_id]
  rw [unitChartPoint, Category.assoc]
  change Spec.map _ ≫ ProjectiveSpace.chartMap K (ULift.{u} (Fin 2)) (Equiv.ulift.symm 1) ≫
      (UniverseReindex.reindexIso K Equiv.ulift).hom = _
  rw [UniverseReindex.chartMap_reindexIso, ← Category.assoc, ← Spec.map_comp]
  rw [ProjectiveLineStandardCharts.right, ← Category.assoc]
  change Spec.map _ ≫ _ = (Spec.map _ ≫ Spec.map _) ≫ _
  rw [← Spec.map_comp]
  congr 1
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply chartRing_hom_ext
  · intro r
    change unitChartEval K (ULift.{u} (Fin 2)) f x (ULift.up 1) b h
      (UniverseReindex.reindexChartRingMap K Equiv.ulift 1
        (chartScalars K (Fin 2) 1 r)) = _
    have hs : UniverseReindex.reindexChartRingMap K Equiv.ulift 1
        (chartScalars K (Fin 2) 1 r) = chartScalars K (ULift.{u} (Fin 2)) (ULift.up 1) r := by
      apply HomogeneousLocalization.val_injective
      simp [UniverseReindex.reindexChartRingMap, chartScalars, constantsToZero,
        HomogeneousLocalization.fromZeroRingHom, HomogeneousLocalization.map_mk]
    rw [hs, unitChartEval_scalar]
    change _ = eval₂RingHom f _ (ProjectiveLineStandardCharts.rightRingEquiv K _)
    simp
  · intro i
    change unitChartEval K (ULift.{u} (Fin 2)) f x (ULift.up 1) b h
      (UniverseReindex.reindexChartRingMap K Equiv.ulift 1 (coordinate K (Fin 2) 1 i)) = _
    rw [UniverseReindex.reindexChartRingMap_coordinate]
    change unitChartEval K (ULift.{u} (Fin 2)) f x (ULift.up 1) b h
      (coordinate K (ULift.{u} (Fin 2)) (ULift.up 1) (ULift.up i)) = _
    rw [unitChartEval_coordinate]
    change _ = eval₂RingHom f _ (ProjectiveLineStandardCharts.rightRingEquiv K _)
    fin_cases i <;> simp [h]

end FLT.Mazur.ProjectiveLine
