/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.DenseClosedRestriction
public import FLT.Mazur.WeierstrassClosureSmoothAmbientProduct
public import FLT.Mazur.WeierstrassGenericKernelSmoothMultiplication

/-!
# Multiplication on the retained smooth kernel intersection

The original generic multiplication preserves the original smooth inclusion.
Schematic density of generic pairs forces the same closed equations integrally,
constructing multiplication on the actual smooth intersection.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R K : Type} [CommRing R] [IsDomain R] [ValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  (W : WeierstrassCurve R) (hΔ : IsUnit (W.map (algebraMap R K)).Δ)
  (G : CommGrp (Over (Spec (.of K)))) (f : G ⟶ integralCurveGroup _ hΔ)
  [IsClosedImmersion f.hom.hom.hom.left]
  [Flat (f.hom.hom.hom.left ≫ integralCurveStructure (W.map (algebraMap R K)))]

local notation "i" => f.hom.hom.hom.left
local notation "s" => genericClosureSmoothStructure W i
local notation "d" => genericKernelToClosureSmooth W hΔ i
local notation "j" => genericClosureSmoothInclusion W i

omit [IsDomain R] [ValuationRing R]
  [Flat (f.hom.hom.hom.left ≫ integralCurveStructure (W.map (algebraMap R K)))] in
/-- The actual generic pair carries ambient integral addition into the original kernel. -/
theorem genericClosureSmoothPair_addition :
    genericClosureSmoothPairMap W hΔ i ≫
        (genericClosureSmoothAmbientPair W i ≫ smoothFactorAddition W) =
      (genericKernelSmoothPairMultiplication W hΔ G f ≫ d) ≫ j := by
  rw [Category.assoc, genericKernelToClosureSmooth_inclusion,
    genericKernelSmoothPairMultiplication_inclusion, ← Category.assoc]
  congr 1
  apply pullback.hom_ext
  · simp only [Category.assoc, genericClosureSmoothAmbientPair_fst,
      genericClosureSmoothPairMap, pullback.map, pullback.lift_fst_assoc, pullback.lift_fst]
    rw [genericKernelToClosureSmooth_inclusion]
  · simp only [Category.assoc, genericClosureSmoothAmbientPair_snd,
      genericClosureSmoothPairMap, pullback.map, pullback.lift_snd_assoc, pullback.lift_snd]
    rw [genericKernelToClosureSmooth_inclusion]

/-- Construct multiplication on the same smooth intersection by its closed equations. -/
def genericClosureSmoothMultiplication : pullback s s ⟶ genericClosureSmoothPart W i := by
  let _ := genericClosureSmoothPairMap_dense W hΔ i
  exact DenseClosedRestriction.lift (genericClosureSmoothPairMap W hΔ i) j
    (genericClosureSmoothAmbientPair W i ≫ smoothFactorAddition W)
    (genericKernelSmoothPairMultiplication W hΔ G f ≫ d)
    (genericClosureSmoothPair_addition W hΔ G f)

/-- The constructed multiplication is exactly the restriction of ambient smooth addition. -/
@[reassoc] theorem genericClosureSmoothMultiplication_inclusion :
    genericClosureSmoothMultiplication W hΔ G f ≫ j =
      genericClosureSmoothAmbientPair W i ≫ smoothFactorAddition W := by
  let _ := genericClosureSmoothPairMap_dense W hΔ i
  exact DenseClosedRestriction.lift_inclusion (genericClosureSmoothPairMap W hΔ i) j
    (genericClosureSmoothAmbientPair W i ≫ smoothFactorAddition W)
    (genericKernelSmoothPairMultiplication W hΔ G f ≫ d)
    (genericClosureSmoothPair_addition W hΔ G f)

/-- The constructed multiplication retains the original generic group multiplication. -/
@[reassoc] theorem genericClosureSmoothPairMap_multiplication :
    genericClosureSmoothPairMap W hΔ i ≫ genericClosureSmoothMultiplication W hΔ G f =
      genericKernelSmoothPairMultiplication W hΔ G f ≫ d := by
  apply (cancel_mono j).mp
  rw [Category.assoc, genericClosureSmoothMultiplication_inclusion,
    genericClosureSmoothPair_addition]

/-- The constructed integral product retains the original coefficient structure. -/
@[reassoc] theorem genericClosureSmoothMultiplication_structure :
    genericClosureSmoothMultiplication W hΔ G f ≫ s = pullback.fst s s ≫ s := by
  calc
    _ = (genericClosureSmoothMultiplication W hΔ G f ≫ j) ≫ integralSmoothStructure W := by
      rw [Category.assoc, genericClosureSmoothInclusion_structure]
    _ = _ := by rw [genericClosureSmoothMultiplication_inclusion,
      genericClosureSmoothAmbientPair_addition_structure]

end FLT.Mazur.WeierstrassIntegralChart
