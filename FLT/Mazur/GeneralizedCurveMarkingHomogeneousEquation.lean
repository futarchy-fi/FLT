/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveMarkingProjectiveSections
public import FLT.Mazur.GeneralizedCurveMarkingComplementEquation

/-!
# The homogeneous equation on the original total space

The original degree-three coordinate sections satisfy the degree-nine
Weierstrass relation as actual global sections, including along the marking.
Faithfulness of Cartier-complement evaluation proves the global identity.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory
namespace FLT.Mazur.GeneralizedEllipticCurve
open FCurve ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle sectionPoleMultiplicativeCoordinates
  Scheme.Modules.pullback ModuleSheafTensor.tensor
  relativePoleFunction

variable {S : Scheme} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  (E : GeneralizedEllipticCurve S) (s : 𝟙_ (Over S) ⟶ E.group)

local notation "t" => s ≫ E.inclusion
local notation "hI" => And.left (smoothMarking_relativeCartier E s)

local instance generalizedCurveMarkingHomogeneousEquationProper :
    IsProper E.curve.hom := E.family.family.1

variable (e : (pullback (s ≫ E.inclusion).left).obj
  (divisorLineBundle (s ≫ E.inclusion).left.ker
    (smoothMarking_relativeCartier E s).1) ≅ structureModule S)

local notation "L" => divisorLineBundle (Scheme.Hom.ker (Over.Hom.left (t))) (hI)
local notation "X" => smoothMarkingProjectiveX E s e
local notation "Y" => smoothMarkingProjectiveY E s e
local notation "Z" => smoothMarkingProjectiveZ E s
local notation "W" => smoothMarkingWeierstrassCurve E s e

/-- The degree-three X section has the same original complement coordinate. -/
theorem smoothMarkingProjectiveX_function : divisorComplementFunction (hI) 3 (X) =
    smoothMarkingComplementX E s e := by
  have h := relativePoleFunction_step E.curve.hom (t).left (hI) 2
    (smoothMarkingFramedLift E s e 1 (by decide))
  unfold relativePoleFunction at h
  unfold smoothMarkingProjectiveX smoothMarkingComplementX relativePoleFunction
  exact h

/-- The degree-three Y section retains the original order-three function. -/
theorem smoothMarkingProjectiveY_function : divisorComplementFunction (hI) 3 (Y) =
    smoothMarkingComplementY E s e := by
  unfold smoothMarkingProjectiveY smoothMarkingComplementY relativePoleFunction
  rfl

omit [IsAffine S] [IsNoetherianRing Γ(S, ⊤)] in
/-- The canonical cube is the constant one in the original affine chart. -/
theorem smoothMarkingProjectiveZ_function : divisorComplementFunction (hI) 3 (Z) = 1 :=
  divisorComplementFunction_power (hI) 3

/-- Multiply three original degree-three sections into the actual degree-nine line. -/
def smoothMarkingCubicProduct (a b c : Γ(tensorPower (L) 3, ⊤)) :
    Γ(tensorPower (L) 9, ⊤) :=
  SectionGradedMultiplication.mul (L) ⊤ 6 3
    (SectionGradedMultiplication.mul (L) ⊤ 3 3 a b) c

omit [IsAffine S] [IsNoetherianRing Γ(S, ⊤)] in
/-- The degree-nine product restricts to multiplication of the three original functions. -/
theorem smoothMarkingCubicProduct_function (a b c : Γ(tensorPower (L) 3, ⊤)) :
    divisorComplementFunction (hI) 9 (smoothMarkingCubicProduct E s a b c) =
      divisorComplementFunction (hI) 3 a * divisorComplementFunction (hI) 3 b *
        divisorComplementFunction (hI) 3 c := by
  unfold smoothMarkingCubicProduct
  rw [divisorComplementFunction_mul (hI) 6 3, divisorComplementFunction_mul (hI) 3 3]

local notation "P" => smoothMarkingCubicProduct E s
local notation "A" => E.curve.hom.appTop

/-- The homogeneous Weierstrass identity holds globally on the original varying family. -/
theorem smoothMarkingProjectiveSections_equation :
    P (Y) (Y) (Z) + A (W).a₁ • P (X) (Y) (Z) + A (W).a₃ • P (Y) (Z) (Z) =
      P (X) (X) (X) + A (W).a₂ • P (X) (X) (Z) + A (W).a₄ • P (X) (Z) (Z) +
        A (W).a₆ • P (Z) (Z) (Z) := by
  apply divisorComplementFunction_injective (hI) 9
  simp only [divisorComplementFunction_add, divisorComplementFunction_smul,
    smoothMarkingCubicProduct_function, smoothMarkingProjectiveX_function,
    smoothMarkingProjectiveY_function, smoothMarkingProjectiveZ_function, mul_one]
  have he := smoothMarkingWeierstrass_equation E s e
  rw [WeierstrassCurve.Affine.equation_iff] at he
  simpa only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, pow_two, pow_succ,
    smoothMarkingComplementBaseMap, RingHom.comp_apply, mul_assoc, pow_zero, mul_one,
    one_mul] using he

end FLT.Mazur.GeneralizedEllipticCurve
