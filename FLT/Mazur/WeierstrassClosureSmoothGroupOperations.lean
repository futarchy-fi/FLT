/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassGenericClosureSmoothMultiplication
public import FLT.Mazur.WeierstrassGenericClosureSmoothOperations

/-!
# The retained smooth kernel operations over the integral base

The original generic group supplies zero and inverse, and dense descent supplies
multiplication. All three operations lie over the original coefficient spectrum
and preserve the actual closed inclusion into the integral smooth group.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj

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
local notation "j" => genericClosureSmoothOverInclusion W i

omit [IsDomain R] [ValuationRing R] [IsFractionRing R K]
  [IsClosedImmersion f.hom.hom.hom.left]
  [Flat (f.hom.hom.hom.left ≫ integralCurveStructure (W.map (algebraMap R K)))] in
/-- The actual generic group's identity is the original cubic identity. -/
@[reassoc] theorem genericKernelGroupZero_inclusion :
    η[G.X].left ≫ i = integralCurveZero (W.map (algebraMap R K)) :=
  congrArg Over.Hom.left (IsMonHom.one_hom f.hom.hom.hom)

omit [IsDomain R] [ValuationRing R] [IsFractionRing R K]
  [IsClosedImmersion f.hom.hom.hom.left]
  [Flat (f.hom.hom.hom.left ≫ integralCurveStructure (W.map (algebraMap R K)))] in
/-- The actual generic group's inverse is the original cubic inverse. -/
@[reassoc] theorem genericKernelGroupNegation_inclusion :
    ι[G.X].left ≫ i = i ≫ integralCurveNegation (W.map (algebraMap R K)) :=
  congrArg Over.Hom.left (GrpObj.inv_hom f.hom.hom.hom)

/-- The retained smooth intersection's identity, over the original integral base. -/
def genericClosureSmoothOverZero : 𝟙_ (Over (Spec (.of R))) ⟶ Over.mk s :=
  Over.homMk (genericClosureSmoothZero W i η[G.X].left
    (genericKernelGroupZero_inclusion W hΔ G f))
    (genericClosureSmoothZero_structure W i _ _)

/-- The retained smooth intersection's inverse, over the original integral base. -/
def genericClosureSmoothOverNegation : Over.mk s ⟶ Over.mk s :=
  Over.homMk (genericClosureSmoothNegation W i ι[G.X].left
    (genericKernelGroupNegation_inclusion W hΔ G f)) (by
      change genericClosureSmoothNegation W i ι[G.X].left _ ≫ s = s
      calc
        _ = (genericClosureSmoothNegation W i ι[G.X].left _ ≫
            genericClosureSmoothInclusion W i) ≫ integralSmoothStructure W := by
          rw [Category.assoc, genericClosureSmoothInclusion_structure]
        _ = _ := by rw [genericClosureSmoothNegation_inclusion, Category.assoc,
          integralSmoothNegation_structure, genericClosureSmoothInclusion_structure])

/-- The constructed multiplication, over the original integral base. -/
def genericClosureSmoothOverMultiplication : Over.mk s ⊗ Over.mk s ⟶ Over.mk s :=
  Over.homMk (genericClosureSmoothMultiplication W hΔ G f)
    (genericClosureSmoothMultiplication_structure W hΔ G f)

omit [IsDomain R] [ValuationRing R] [IsClosedImmersion f.hom.hom.hom.left]
  [Flat (f.hom.hom.hom.left ≫ integralCurveStructure (W.map (algebraMap R K)))] in
/-- The identity retains the original ambient smooth identity. -/
theorem genericClosureSmoothOverZero_inclusion :
    genericClosureSmoothOverZero W hΔ G f ≫ j = integralSmoothOverZero W := by
  apply Over.OverMorphism.ext
  exact genericClosureSmoothZero_inclusion W i _ _

omit [IsDomain R] [ValuationRing R] [IsFractionRing R K]
  [Flat (f.hom.hom.hom.left ≫ integralCurveStructure (W.map (algebraMap R K)))] in
/-- The inverse retains the original ambient smooth inverse. -/
theorem genericClosureSmoothOverNegation_inclusion :
    genericClosureSmoothOverNegation W hΔ G f ≫ j = j ≫ integralSmoothOverNegation W := by
  apply Over.OverMorphism.ext
  exact genericClosureSmoothNegation_inclusion W i _ _

/-- Multiplication retains the actual ambient smooth product on both original inclusions. -/
theorem genericClosureSmoothOverMultiplication_inclusion :
    genericClosureSmoothOverMultiplication W hΔ G f ≫ j =
      (j ⊗ₘ j) ≫ integralSmoothOverAddition W := by
  apply Over.OverMorphism.ext
  change genericClosureSmoothMultiplication W hΔ G f ≫ genericClosureSmoothInclusion W i =
    (j ⊗ₘ j).left ≫ smoothFactorAddition W
  rw [genericClosureSmoothOverInclusion_tensor, genericClosureSmoothMultiplication_inclusion]

end FLT.Mazur.WeierstrassIntegralChart
