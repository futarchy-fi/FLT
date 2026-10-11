/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonMarkedSections

/-!
# Scaling the original labeled polygon markings

The existing polygon scaling automorphism multiplies the actual unit coordinate
of every marked section. In particular it moves any prescribed unit marking to one.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonMarkedScaling
open PolygonPinching ProjectiveLineActionSpecialization
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable (K : Type u) [Field K]

/-- Scaling the original projective-line unit point multiplies its coordinate. -/
@[reassoc] theorem unitPoint_scaling (a b : Kˣ) :
    unitPoint K a ≫ (torusToComponent K).left ≫ ProjectiveLine.scaling K b =
      unitPoint K (a * b) ≫ (torusToComponent K).left := by
  change unitPoint K a ≫ (ProjectiveLine.overlapLeft K ≫ ProjectiveLine.left K) ≫ _ =
    unitPoint K (a * b) ≫ ProjectiveLine.overlapLeft K ≫ ProjectiveLine.left K
  rw [Category.assoc, ProjectiveLine.left_scaling]
  suffices he : unitPoint K a ≫ ProjectiveLine.overlapLeft K ≫
      ProjectiveLine.chartScaling K b = unitPoint K (a * b) ≫ ProjectiveLine.overlapLeft K by
    simpa only [Category.assoc] using congrArg (fun f => f ≫ ProjectiveLine.left K) he
  change Spec.map _ ≫ Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  change ((LaurentUnitPoints.evalUnit (R := K) a).toRingHom.comp
    (Polynomial.toLaurent.comp (PolygonChartScaling.affine b))) =
      (LaurentUnitPoints.evalUnit (R := K) (a * b)).toRingHom.comp Polynomial.toLaurent
  apply Polynomial.ringHom_ext
  · intro r
    simp
  · change LaurentUnitPoints.evalUnit (R := K) a
      (Polynomial.toLaurent (PolygonChartScaling.affine b Polynomial.X)) =
        LaurentUnitPoints.evalUnit (R := K) (a * b) (Polynomial.toLaurent Polynomial.X)
    rw [PolygonChartScaling.affine_X, map_mul, Polynomial.toLaurent_C,
      Polynomial.toLaurent_X, map_mul, LaurentUnitPoints.evalUnit_C,
      LaurentUnitPoints.evalUnit_T, LaurentUnitPoints.evalUnit_T]
    simp only [zpow_one]
    exact mul_comm (b : K) (a : K)

variable (n : ℕ) (hn : 0 < n) {C : Over (Spec (.of K))}
  (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)

/-- The original labeled section keeps its label and has its unit coordinate multiplied. -/
@[reassoc] theorem section_scaling (a b : Kˣ) (i : Fin n) :
    PolygonMarkedSections.sectionMap K n p a i ≫ (polygonScaling K hn p q h b).left =
      PolygonMarkedSections.sectionMap K n p (a * b) i := by
  have he := congrArg Over.Hom.left (componentι_polygonScaling K hn p q h b i)
  simp only [Over.comp_left] at he
  simp only [PolygonMarkedSections.sectionMap, Over.comp_left, Category.assoc]
  rw [he]
  change unitPoint K a ≫ (torusToComponent K).left ≫
    ProjectiveLine.scaling K b ≫ (componentι K n i).left ≫ p.left = _
  rw [unitPoint_scaling_assoc]

/-- Inverse scaling sends any prescribed unit marking to the original identity marking. -/
@[reassoc] theorem section_inverse_scaling (a : Kˣ) (i : Fin n) :
    PolygonMarkedSections.sectionMap K n p a i ≫ (polygonScaling K hn p q h a⁻¹).left =
      PolygonMarkedSections.sectionMap K n p 1 i := by
  rw [section_scaling, mul_inv_cancel]

end FLT.Mazur.PolygonMarkedScaling
