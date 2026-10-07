/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassAdditionStructure

/-!
# The zero section and its two product sections

The point [0:1:0] gives a section over the whole coefficient spectrum.
Its left and right pairings with the identity are actual maps to the fiber
product, with explicit restrictions to the tensor input charts.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The infinity point as a section of the glued integral cubic. -/
def integralCurveZero : Spec (.of R) ⟶ integralCurve W :=
  Spec.map (CommRingCat.ofHom (chartInfinityEvaluation (S := R) W).toRingHom) ≫
    integralCurveChart W 1

/-- The infinity point is defined over the entire coefficient scheme. -/
theorem integralCurveZero_structure :
    integralCurveZero W ≫ integralCurveStructure W = 𝟙 _ := by
  rw [integralCurveZero, Category.assoc, integralCurveChart_structure,
    chartStructure, specAlgHom_structure]
  exact Spec.map_id _

/-- Extending the base infinity evaluation gives the infinity point over every algebra. -/
theorem chartInfinityEvaluation_base {S : Type u} [CommRing S] [Algebra R S] :
    (chartInfinityEvaluation (S := S) W).toRingHom =
      (algebraMap R S).comp (chartInfinityEvaluation (S := R) W).toRingHom := by
  have h : chartInfinityEvaluation (S := S) W =
      (Algebra.ofId R S).comp (chartInfinityEvaluation (S := R) W) := by
    apply hom_ext
    intro i
    fin_cases i <;> simp
  exact congrArg AlgHom.toRingHom h

/-- Pair zero on the left with the universal curve point. -/
def integralCurveLeftZero : integralCurve W ⟶ integralCurveProduct W :=
  pullback.lift (integralCurveStructure W ≫ integralCurveZero W) (𝟙 _)
    (by rw [Category.assoc, integralCurveZero_structure, Category.comp_id, Category.id_comp])

/-- Pair the universal curve point with zero on the right. -/
def integralCurveRightZero : integralCurve W ⟶ integralCurveProduct W :=
  pullback.lift (𝟙 _) (integralCurveStructure W ≫ integralCurveZero W)
    (by rw [Category.assoc, integralCurveZero_structure, Category.comp_id, Category.id_comp])

/-- The first projection of the left-zero section is the base-valued zero. -/
theorem integralCurveLeftZero_fst :
    integralCurveLeftZero W ≫ pullback.fst _ _ =
      integralCurveStructure W ≫ integralCurveZero W := pullback.lift_fst ..

/-- The second projection of the left-zero section is the original point. -/
theorem integralCurveLeftZero_snd :
    integralCurveLeftZero W ≫ pullback.snd _ _ = 𝟙 _ := pullback.lift_snd ..

/-- The first projection of the right-zero section is the original point. -/
theorem integralCurveRightZero_fst :
    integralCurveRightZero W ≫ pullback.fst _ _ = 𝟙 _ := pullback.lift_fst ..

/-- The second projection of the right-zero section is the base-valued zero. -/
theorem integralCurveRightZero_snd :
    integralCurveRightZero W ≫ pullback.snd _ _ =
      integralCurveStructure W ≫ integralCurveZero W := pullback.lift_snd ..

/-- The left-zero section restricts to the original tensor evaluation on both curve charts. -/
theorem integralCurveChart_leftZero (b : Bool) :
    integralCurveChart W (productChartCoordinate b) ≫ integralCurveLeftZero W =
      Spec.map (CommRingCat.ofHom
        (chartProductAtLeftInfinity W (productChartCoordinate b)).toRingHom) ≫
          integralCurveProductChart W true b := by
  apply pullback.hom_ext
  · simp only [Category.assoc, integralCurveLeftZero_fst, integralCurveProductChart_fst]
    rw [← Category.assoc, integralCurveChart_structure]
    rw [integralCurveZero, chartStructure, ← Category.assoc, ← Spec.map_comp,
      ← Category.assoc,
      ← Spec.map_comp]
    congr 1
    change Spec.map (CommRingCat.ofHom
      ((algebraMap R _).comp (chartInfinityEvaluation (S := R) W).toRingHom)) =
      Spec.map (CommRingCat.ofHom
        ((chartProductAtLeftInfinity W _).comp (chartProductLeft W 1 _)).toRingHom)
    rw [chartProductAtLeftInfinity_left,
      chartInfinityEvaluation_base (S := Coordinate W (productChartCoordinate b))]
  · simp only [Category.assoc, integralCurveLeftZero_snd, Category.comp_id,
      integralCurveProductChart_snd]
    rw [← Category.assoc, ← Spec.map_comp]
    change _ = Spec.map (CommRingCat.ofHom
      ((chartProductAtLeftInfinity W _).comp (chartProductRight W 1 _)).toRingHom) ≫ _
    rw [chartProductAtLeftInfinity_right]
    simp

/-- The right-zero section restricts to the opposite tensor evaluation. -/
theorem integralCurveChart_rightZero (b : Bool) :
    integralCurveChart W (productChartCoordinate b) ≫ integralCurveRightZero W =
      Spec.map (CommRingCat.ofHom
        (chartProductAtRightInfinity W (productChartCoordinate b)).toRingHom) ≫
          integralCurveProductChart W b true := by
  apply pullback.hom_ext
  · simp only [Category.assoc, integralCurveRightZero_fst, Category.comp_id,
      integralCurveProductChart_fst]
    rw [← Category.assoc, ← Spec.map_comp]
    change _ = Spec.map (CommRingCat.ofHom
      ((chartProductAtRightInfinity W _).comp (chartProductLeft W _ 1)).toRingHom) ≫ _
    rw [chartProductAtRightInfinity_left]
    simp
  · simp only [Category.assoc, integralCurveRightZero_snd, integralCurveProductChart_snd]
    rw [← Category.assoc, integralCurveChart_structure]
    rw [integralCurveZero, chartStructure, ← Category.assoc, ← Spec.map_comp,
      ← Category.assoc,
      ← Spec.map_comp]
    congr 1
    change Spec.map (CommRingCat.ofHom
      ((algebraMap R _).comp (chartInfinityEvaluation (S := R) W).toRingHom)) =
      Spec.map (CommRingCat.ofHom
        ((chartProductAtRightInfinity W _).comp (chartProductRight W _ 1)).toRingHom)
    rw [chartProductAtRightInfinity_right,
      chartInfinityEvaluation_base (S := Coordinate W (productChartCoordinate b))]

end FLT.Mazur.WeierstrassIntegralChart
