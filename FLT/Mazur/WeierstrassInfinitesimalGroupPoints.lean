/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassInfinitesimalAddition
public import FLT.Mazur.WeierstrassIntegralGroup

/-!
# Infinitesimal parameters in the original scheme group

The square-zero chart parametrization defines actual points of the constructed
Weierstrass group, and its local addition calculation agrees with global
addition. The resulting injective additive map excludes prime-to-characteristic
torsion among these infinitesimal identity-chart points.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonObj

namespace FLT.Mazur.WeierstrassIntegralChart

universe u
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ) (I : Ideal A) (hI : I ^ 2 = ⊥)

/-- An infinitesimal parameter as an actual relative point of the original group scheme. -/
def infinitesimalGroupPoint (x : I) :
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A))) ⟶ (integralCurveGroup W hΔ).X :=
  Over.homMk (Spec.map (CommRingCat.ofHom (infinitesimalChartPoint W I hI x).val.toRingHom) ≫
    integralCurveChart W 1) (by
      change (_ ≫ _) ≫ integralCurveStructure W = _
      rw [Category.assoc, integralCurveChart_structure, chartStructure, specAlgHom_structure]
      rfl)

/-- The original X coordinate distinguishes the infinitesimal group points. -/
theorem infinitesimalGroupPoint_injective :
    Function.Injective (infinitesimalGroupPoint W hΔ I hI) := by
  intro x y h
  have he := congrArg Over.Hom.left h
  change Spec.map _ ≫ integralCurveChart W 1 = Spec.map _ ≫ integralCurveChart W 1 at he
  have he' := Spec.map_injective ((cancel_mono (integralCurveChart W 1)).mp he)
  apply Subtype.ext
  have hcoord := congrArg (fun g : CommRingCat.of (Coordinate W 1) ⟶ CommRingCat.of A ↦
    g.hom (coord W 1 0)) he'
  change (infinitesimalChartPoint W I hI x).val (coord W 1 0) =
    (infinitesimalChartPoint W I hI y).val (coord W 1 0) at hcoord
  simpa only [infinitesimalChartPoint_x] using hcoord

/-- The product-algebra point gives the actual pair of global infinitesimal group points. -/
theorem infinitesimalPairEvaluation_global (x y : I) :
    Spec.map (CommRingCat.ofHom (infinitesimalPairEvaluation W I hI x y).toRingHom) ≫
        integralCurveProductChart W true true =
      pullback.lift (f := integralCurveStructure W) (g := integralCurveStructure W)
        (infinitesimalGroupPoint W hΔ I hI x).left
        (infinitesimalGroupPoint W hΔ I hI y).left
        ((infinitesimalGroupPoint W hΔ I hI x).w.trans
          (infinitesimalGroupPoint W hΔ I hI y).w.symm) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, integralCurveProductChart_fst, productChartCoordinate,
      pullback.lift_fst]
    rw [← Category.assoc, ← Spec.map_comp]
    change Spec.map (CommRingCat.ofHom
      ((infinitesimalPairEvaluation W I hI x y).comp (chartProductLeft W 1 1)).toRingHom) ≫ _ = _
    rw [infinitesimalPairEvaluation, chartProductEvaluation_left]
    rfl
  · simp only [Category.assoc, integralCurveProductChart_snd, productChartCoordinate,
      pullback.lift_snd]
    rw [← Category.assoc, ← Spec.map_comp]
    change Spec.map (CommRingCat.ofHom
      ((infinitesimalPairEvaluation W I hI x y).comp (chartProductRight W 1 1)).toRingHom) ≫ _ = _
    rw [infinitesimalPairEvaluation, chartProductEvaluation_right]
    rfl

/-- The original global group law adds the square-zero parameters. -/
theorem infinitesimalGroupPoint_add (x y : I) :
    infinitesimalGroupPoint W hΔ I hI (x + y) =
      infinitesimalGroupPoint W hΔ I hI x * infinitesimalGroupPoint W hΔ I hI y := by
  apply Over.OverMorphism.ext
  change _ = pullback.lift (infinitesimalGroupPoint W hΔ I hI x).left
    (infinitesimalGroupPoint W hΔ I hI y).left
    ((infinitesimalGroupPoint W hΔ I hI x).w.trans
      (infinitesimalGroupPoint W hΔ I hI y).w.symm) ≫ integralCurveAddition W hΔ
  rw [← infinitesimalPairEvaluation_global W hΔ I hI, Category.assoc]
  have hl : Spec.map (CommRingCat.ofHom
      (infinitesimalPairEvaluation W I hI x y).toRingHom) =
      Spec.map (CommRingCat.ofHom (infinitesimalAdditionLift W I hI x y).toRingHom) ≫
        infinityAdditionInclusion W := by
    rw [infinityAdditionInclusion, ← Spec.map_comp]
    exact congrArg (fun f : ChartProduct W 1 1 →ₐ[R] A ↦
      Spec.map (CommRingCat.ofHom f.toRingHom))
      (infinitesimalAdditionLift_restriction W I hI x y).symm
  rw [hl, Category.assoc, integralCurveAddition_infinity, ← Category.assoc]
  rw [infinityAdditionSpec, ← Spec.map_comp]
  change _ = Spec.map (CommRingCat.ofHom
    ((infinitesimalAdditionLift W I hI x y).comp (infinityAdditionChart W)).toRingHom) ≫ _
  rw [infinityAdditionChart_infinitesimal]
  rfl

/-- The actual infinitesimal group points form an additive copy of the square-zero ideal. -/
def infinitesimalGroupPointAddHom : I →+
    Additive (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A))) ⟶
      (integralCurveGroup W hΔ).X) :=
  AddMonoidHom.mk' (fun x ↦ Additive.ofMul (infinitesimalGroupPoint W hΔ I hI x))
    (infinitesimalGroupPoint_add W hΔ I hI)

/-- Prime-to-characteristic torsion in the infinitesimal identity chart is trivial. -/
theorem infinitesimalGroupPoint_torsion (n : ℕ) (hn : IsUnit (n : A)) (x : I)
    (hx : infinitesimalGroupPoint W hΔ I hI x ^ n = 1) : x = 0 := by
  have hinj : Function.Injective (infinitesimalGroupPointAddHom W hΔ I hI) :=
    infinitesimalGroupPoint_injective W hΔ I hI
  have he : n • x = 0 := hinj (by
    simpa only [map_nsmul, map_zero, infinitesimalGroupPointAddHom,
      AddMonoidHom.mk'_apply, ofMul_pow, ofMul_one] using congrArg Additive.ofMul hx)
  apply Subtype.ext
  have hz : (n : A) * (x : A) = 0 := by
    have hz := congrArg (fun a : I ↦ (a : A)) he
    change n • (x : A) = 0 at hz
    rwa [nsmul_eq_mul] at hz
  exact hn.mul_right_eq_zero.mp hz

end FLT.Mazur.WeierstrassIntegralChart
