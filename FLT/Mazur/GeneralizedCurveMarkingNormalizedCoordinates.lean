/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionPoleNormalizedDifference
public import FLT.Mazur.GeneralizedCurveMarkingPoleTwoExpansion
public import FLT.Mazur.GeneralizedCurveMarkingFrameScaling

/-!
# Coordinate corrections for independently normalized original pole sections

Arbitrary normalized order-two and order-three sections on the original
family have the integral triangular change formula. The lower coefficients
are extracted from the actual canonical and order-two bases, not assumed.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory
namespace FLT.Mazur.GeneralizedEllipticCurve
open FCurve ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle ModuleSheafTensor.tensor
  Scheme.Modules.pullback sectionPoleMultiplicativeCoordinates relativePoleFunction
variable {S : Scheme} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  (E : GeneralizedEllipticCurve S) (s : 𝟙_ (Over S) ⟶ E.group)
local notation "t" => s ≫ E.inclusion
local notation "hI" => And.left (smoothMarking_relativeCartier E s)
local notation "L" => divisorLineBundle (Scheme.Hom.ker (Over.Hom.left (t))) (hI)

local instance generalizedCurveMarkingNormalizedCoordinatesProper :
    IsProper E.curve.hom := E.family.family.1

variable (e f : (pullback (s ≫ E.inclusion).left).obj
  (divisorLineBundle (s ≫ E.inclusion).left.ker
    (smoothMarking_relativeCartier E s).1) ≅ structureModule S)
local notation "u" => Units.val (smoothMarkingFrameUnit E s e f)
local notation "φ" => smoothMarkingComplementBaseMap E s

/-- An independently normalized order-two section differs by an actual base constant. -/
theorem smoothMarkingNormalizedX_correction
    (x : ModuleRingH E.curve.hom.appTop.hom (tensorPower (L) 2) 0)
    (hx : sectionPoleCoefficient (t).left (hI) f 2 (moduleH0Equiv _ x) = 1) :
    ∃ r : Γ(S, ⊤), relativePoleFunction E.curve.hom (t).left (hI) 2 x =
      φ (u ^ 2) * smoothMarkingComplementX E s e + φ r := by
  rw [sectionPoleCoefficient_leading (t).left (hI) f E.curve.hom (t).w 1] at hx
  have hy := smoothMarkingFramedLift_coefficient E s e 1 (by decide)
  rw [sectionPoleCoefficient_leading (t).left (hI) e E.curve.hom (t).w 1] at hy
  obtain ⟨z, hz, _⟩ := sectionPoleNormalizedDifference_existsUnique E.curve.hom
    (t).left (t).w (hI) e f 1 x (smoothMarkingFramedLift E s e 1 (by decide)) hx hy
  let r := (smoothMarkingOneBasis E s).repr z ()
  have hr : r • smoothMarkingOneBasis E s () = z := by
    simpa only [Fintype.sum_unique] using (smoothMarkingOneBasis E s).sum_repr z
  refine ⟨r, ?_⟩
  have h := congrArg (relativePoleFunctionAddHom E.curve.hom (t).left (hI) 2) hz
  rw [map_add] at h
  change relativePoleFunction E.curve.hom (t).left (hI) 2 x =
    relativePoleFunction E.curve.hom (t).left (hI) 2
      (u ^ 2 • smoothMarkingFramedLift E s e 1 (by decide)) +
    relativePoleFunction E.curve.hom (t).left (hI) 2
      (divisorPowerRingStep E.curve.hom.appTop.hom (hI) 1 z) at h
  simpa only [relativePoleFunction_smul, relativePoleFunction_step, ← hr,
    smoothMarkingComplement_oneBasis, mul_one, smoothMarkingComplementX,
    smoothMarkingComplementBaseMap, RingHom.comp_apply] using h

/-- An independently normalized order-three section has the actual lower affine correction. -/
theorem smoothMarkingNormalizedY_correction
    (y : ModuleRingH E.curve.hom.appTop.hom (tensorPower (L) 3) 0)
    (hy : sectionPoleCoefficient (t).left (hI) f 3 (moduleH0Equiv _ y) = 1) :
    ∃ b c : Γ(S, ⊤), relativePoleFunction E.curve.hom (t).left (hI) 3 y =
      φ (u ^ 3) * smoothMarkingComplementY E s e +
        (φ c + φ b * smoothMarkingComplementX E s e) := by
  rw [sectionPoleCoefficient_leading (t).left (hI) f E.curve.hom (t).w 2] at hy
  have hz := smoothMarkingFramedLift_coefficient E s e 2 (by decide)
  rw [sectionPoleCoefficient_leading (t).left (hI) e E.curve.hom (t).w 2] at hz
  obtain ⟨z, hz, _⟩ := sectionPoleNormalizedDifference_existsUnique E.curve.hom
    (t).left (t).w (hI) e f 2 y (smoothMarkingFramedLift E s e 2 (by decide)) hy hz
  let B := smoothMarkingTwoBasis E s
    (sectionPoleMultiplicativeCoordinates (t).left (hI) e 2)
  refine ⟨B.repr z (Sum.inr ()), B.repr z (Sum.inl ()), ?_⟩
  have h := congrArg (relativePoleFunctionAddHom E.curve.hom (t).left (hI) 3) hz
  rw [map_add] at h
  change relativePoleFunction E.curve.hom (t).left (hI) 3 y =
    relativePoleFunction E.curve.hom (t).left (hI) 3
      (u ^ 3 • smoothMarkingFramedLift E s e 2 (by decide)) +
    relativePoleFunction E.curve.hom (t).left (hI) 3
      (divisorPowerRingStep E.curve.hom.appTop.hom (hI) 2 z) at h
  simpa only [relativePoleFunction_smul, relativePoleFunction_step,
    smoothMarkingPoleTwo_function E s e, smoothMarkingComplementY,
    smoothMarkingComplementBaseMap, RingHom.comp_apply] using h

end FLT.Mazur.GeneralizedEllipticCurve
