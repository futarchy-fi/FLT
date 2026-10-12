/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearTensorInput
public import FLT.Mazur.WeierstrassModificationXTensorContraction
public import FLT.Mazur.WeierstrassDividedTerminalParameterStructure
public import FLT.Mazur.WeierstrassRootShearUnitAddition

/-!
# The actual scale-one tensor chart has a smooth input

The original ordered tangent ratio constructs a smooth lift with its full
coefficient structure and original integral cubic contraction.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassModificationX
open WeierstrassIntegralChart WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)
  (S : Type) [CommRing S] [Algebra R S] (r : S)
  (hs : algebraMap R S s = 1) (hb3 : algebraMap R S b3 = 0)
  (hb4 : algebraMap R S b4 = 0) (hb6 : algebraMap R S b6 = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
  (a : Sˣ) (ha : (a : S) = (W.map (algebraMap R S)).a₁ + 2 * r)
local notation "V" => W.map (algebraMap R S)
local notation "T" => ScalarExtension W s b3 b4 b6 S
local notation "L" => tensorShearScaleOneLaurentMap W s b3 b4 b6 S r hs hb3 hb4 hb6 hr
local notation "hc" => tensorOriginal_nodal_coefficients W s b3 b4 b6 h3 h4 h6 S hb3 hb4 hb6
local notation "I" => rootShearTorusSmoothIso V r a ha hr (hc).1 (hc).2.1 (hc).2.2

/-- The original tensor chart maps to the smooth locus through its actual tangent ratio. -/
def tensorShearScaleOneSmoothInput : Spec (.of T) ⟶ (integralSmoothOpen V).toScheme :=
  Spec.map (CommRingCat.ofHom (L).toRingHom) ≫ (I).hom

local notation "P" => tensorShearScaleOneSmoothInput W s b3 b4 b6 h3 h4 h6 S r
  hs hb3 hb4 hb6 hr a ha

/-- The smooth lift is precisely the unit input of the original ordered tangent ratio. -/
theorem tensorShearScaleOneSmoothInput_unit :
    P = (rootShearSmoothUnitInput V r a ha hr (hc).1 (hc).2.1 (hc).2.2
      (tensorShearScaleOneParameter W s b3 b4 b6 S r hs hb3 hb4 hb6 hr)).left := rfl

/-- The smooth lift retains the whole affine cubic input. -/
@[reassoc] theorem tensorShearScaleOneSmoothInput_inclusion :
    P ≫ (integralSmoothOpen V).ι =
      Spec.map (CommRingCat.ofHom
        (tensorOriginalAffineMap W s b3 b4 b6 h3 h4 h6 S).toRingHom) ≫
          integralCurveChart V 2 := by
  rw [tensorShearScaleOneSmoothInput, Category.assoc]
  exact (tensorShearScaleOne_originalInput W s b3 b4 b6 h3 h4 h6 S r
    hs hb3 hb4 hb6 hr a ha).symm

/-- The constructed smooth input preserves the actual tensor coefficient structure. -/
@[reassoc] theorem tensorShearScaleOneSmoothInput_structure :
    P ≫ integralSmoothStructure V =
      Spec.map (CommRingCat.ofHom (algebraMap S T)) := by
  rw [tensorShearScaleOneSmoothInput, Category.assoc, rootShearTorusSmoothIso_structure]
  exact terminalComponent_algebra_structure L

/-- The smooth lift reconstructs the original integral incidence-chart contraction. -/
@[reassoc] theorem tensorShearScaleOneSmoothInput_original :
    P ≫ (integralSmoothOpen V).ι ≫ integralCoefficientMorphism W =
      TensorOpenChart.projection ≫ toCurve W s b3 b4 b6 h3 h4 h6 := by
  rw [tensorShearScaleOneSmoothInput_inclusion_assoc,
    tensorOriginalAffineMap_toCurve]

end FLT.Mazur.WeierstrassModificationX
