/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointProjectiveSections
public import FLT.Mazur.PolygonCompletePointComplementEquation

/-!
# The integral homogeneous equation on the original total space

Faithful evaluation on the Cartier complement lifts the actual equation of
functions to the degree-nine homogeneous relation, including along the marking.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve FCurve.ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  divisorLineBundle ModuleSheafTensor.tensor relativePoleFunction

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "f" => exactVeroneseProjToBase K n h
local notation "s" => completeBaseMarking K n h i
local notation "hI" => And.left (completeBaseMarking_relativeCartier K n h i)

local notation "L" => divisorLineBundle (Scheme.Hom.ker (s)) hI
local notation "X" => completePointProjectiveX K n h i
local notation "Y" => completePointProjectiveY K n h i
local notation "Z" => completePointProjectiveZ K n h i
local notation "W" => completePointWeierstrassCurve K n h i

/-- The degree-three X section has the same original complement coordinate. -/
theorem completePointProjectiveX_function : divisorComplementFunction hI 3 (X) =
    completePointComplementX K n h i := by
  have he := relativePoleFunction_step f s hI 2
    (completePointPoleLift K n h i 0)
  unfold relativePoleFunction at he
  unfold completePointProjectiveX completePointComplementX relativePoleFunction
  exact he

/-- The degree-three Y section retains the original order-three function. -/
theorem completePointProjectiveY_function : divisorComplementFunction hI 3 (Y) =
    completePointComplementY K n h i := by
  unfold completePointProjectiveY completePointComplementY relativePoleFunction
  rfl

/-- The canonical cube is the constant one in the original affine chart. -/
theorem completePointProjectiveZ_function : divisorComplementFunction hI 3 (Z) = 1 :=
  divisorComplementFunction_power hI 3

/-- Multiply three original degree-three sections into the actual degree-nine line. -/
def completePointCubicProduct (a b c : Γ(tensorPower (L) 3, ⊤)) :
    Γ(tensorPower (L) 9, ⊤) :=
  SectionGradedMultiplication.mul (L) ⊤ 6 3
    (SectionGradedMultiplication.mul (L) ⊤ 3 3 a b) c

/-- The degree-nine product restricts to multiplication of the three original functions. -/
theorem completePointCubicProduct_function (a b c : Γ(tensorPower (L) 3, ⊤)) :
    divisorComplementFunction hI 9 (completePointCubicProduct K n h i a b c) =
      divisorComplementFunction hI 3 a * divisorComplementFunction hI 3 b *
        divisorComplementFunction hI 3 c := by
  unfold completePointCubicProduct
  rw [divisorComplementFunction_mul hI 6 3, divisorComplementFunction_mul hI 3 3]

local notation "P" => completePointCubicProduct K n h i
local notation "A" => Scheme.Hom.appTop (f)

/-- The homogeneous Weierstrass identity holds globally on the original varying family. -/
theorem completePointProjectiveSections_equation :
    P (Y) (Y) (Z) + A (W).a₁ • P (X) (Y) (Z) + A (W).a₃ • P (Y) (Z) (Z) =
      P (X) (X) (X) + A (W).a₂ • P (X) (X) (Z) + A (W).a₄ • P (X) (Z) (Z) +
        A (W).a₆ • P (Z) (Z) (Z) := by
  apply divisorComplementFunction_injective hI 9
  simp only [divisorComplementFunction_add, divisorComplementFunction_smul,
    completePointCubicProduct_function, completePointProjectiveX_function,
    completePointProjectiveY_function, completePointProjectiveZ_function, mul_one]
  have he := completePointWeierstrass_equation K n h i
  rw [WeierstrassCurve.Affine.equation_iff] at he
  simpa only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, pow_two, pow_succ,
    completePointComplementBaseMap, RingHom.comp_apply, mul_assoc, pow_zero, mul_one,
    one_mul] using he

end FLT.Mazur.PolygonInfinitesimalStages
