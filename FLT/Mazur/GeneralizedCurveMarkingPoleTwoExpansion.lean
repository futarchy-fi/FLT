/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveMarkingComplementCoordinates
public import FLT.Mazur.RelativePoleComplementLinear

/-!
# Expanding every original order-two pole section

The normalized basis retains the canonical constant section. Every actual
order-two section therefore evaluates to a unique pair of scalar coefficients
in the original functions 1 and x, across singular and reducible fibers.
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

local instance generalizedCurveMarkingPoleTwoExpansionProper :
    IsProper E.curve.hom := E.family.family.1

variable (e : (pullback (s ≫ E.inclusion).left).obj
  (divisorLineBundle (s ≫ E.inclusion).left.ker
    (smoothMarking_relativeCartier E s).1) ≅ structureModule S)
local notation "B" => smoothMarkingTwoBasis E s
  (sectionPoleMultiplicativeCoordinates (Over.Hom.left (t)) (hI) e 2)

/-- The constant vector of the original order-two basis is the original canonical inclusion. -/
theorem smoothMarkingTwoBasis_constant :
    (B) (Sum.inl ()) = divisorPowerRingStep E.curve.hom.appTop.hom (hI) 1
      (smoothMarkingOneBasis E s ()) := by
  let _ : Subsingleton (ModuleH (tensorPower (L) 1) 1) :=
    smoothMarkingPower_relative_acyclic E s 1 (by decide) 0
  exact sectionPoleAdaptedBasis_old E.curve.hom (t).left (t).w (hI) 1 _ _ ()

/-- The order-two basis evaluates to the retained original functions 1 and x. -/
theorem smoothMarkingComplement_twoBasis (i : Unit ⊕ Unit) :
    relativePoleFunction E.curve.hom (t).left (hI) 2 ((B) i) =
      Sum.elim (fun _ ↦ 1) (fun _ ↦ smoothMarkingComplementX E s e) i := by
  rcases i with u | u <;> cases u
  · rw [smoothMarkingTwoBasis_constant, relativePoleFunction_step,
      smoothMarkingComplement_oneBasis]
    rfl
  · rw [smoothMarkingTwoBasis_new]
    rfl

/-- The actual basis coefficients give the affine expansion of every original order-two section. -/
theorem smoothMarkingPoleTwo_function
    (z : ModuleRingH E.curve.hom.appTop.hom (tensorPower (L) 2) 0) :
    relativePoleFunction E.curve.hom (t).left (hI) 2 z =
      smoothMarkingComplementBaseMap E s ((B).repr z (Sum.inl ())) +
        smoothMarkingComplementBaseMap E s ((B).repr z (Sum.inr ())) *
          smoothMarkingComplementX E s e := by
  have h := congrArg (relativePoleFunctionAddHom E.curve.hom (t).left (hI) 2)
    ((B).sum_repr z)
  rw [map_sum] at h
  change (∑ i, relativePoleFunction E.curve.hom (t).left (hI) 2
    ((B).repr z i • (B) i)) = relativePoleFunction E.curve.hom (t).left (hI) 2 z at h
  simpa only [relativePoleFunction_smul, smoothMarkingComplement_twoBasis,
    Fintype.sum_sum_type, Fintype.sum_unique, Sum.elim_inl, Sum.elim_inr, mul_one,
    smoothMarkingComplementBaseMap, RingHom.comp_apply] using h.symm

end FLT.Mazur.GeneralizedEllipticCurve
