/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticLayerQuotient

/-!
# The first parameter image is the preceding stage line

The affine flatness calculation identifies the annihilator of the parameter
with its last-power image. Thus multiplication by the original parameter
identifies the adjacent quotient line with the first parameter image sheaf.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules

namespace FLT.Mazur.PolygonArithmeticStages

open FCurve ModuleLineBundleTensorPullback IdealAdicQuotient
open GlobalIdealPower IdealPowerScalarLift

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (A : Type) [CommRing A] [IsDomain A] (π : A) (hπ : π ≠ 0) (m n : ℕ) (h : 2 ≤ n) (d : ℕ)

include hπ in
/-- On every affine open, the parameter annihilator is the actual last-power ideal image. -/
theorem boundaryPower_parameter_annihilator
    (U : (family A π (m + 1) n h).left.affineOpens)
    (s : Γ(tensorPower (boundaryLine A π (m + 1) n h) d, U.1)) :
    (family A π (m + 1) n h).left.presheaf.map U.1.leTop.op
        (stageParameterSection A π (m + 1) n h) • s = 0 ↔
      s ∈ (stageParameterIdeal A π (m + 1) n h ^ (m + 1)).ideal U •
        (⊤ : Submodule Γ((family A π (m + 1) n h).left, U.1)
          Γ(tensorPower (boundaryLine A π (m + 1) n h) d, U.1)) := by
  let _ := boundaryPowerSections_flat A π (m + 1) n h d U.1 U.2
  rw [stageParameterPower_ideal, Submodule.ideal_span_singleton_smul]
  simp only [Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top, true_and]
  have he := FlatScalarExactness.smul_eq_zero_iff
    (boundaryPowerSections A π (m + 1) n h d U.1)
    (parameter A π (m + 1) ^ (m + 1)) (parameter A π (m + 1))
    (fun z ↦ (parameter_mul_eq_zero_iff A π hπ m z).trans
      (restriction_eq_zero_iff A π m z)) s
  change (family A π (m + 1) n h).left.presheaf.map U.1.leTop.op
      (stageScalars A π (m + 1) n h (parameter A π (m + 1))) • s = 0 ↔
    ∃ y, (family A π (m + 1) n h).left.presheaf.map U.1.leTop.op
      (stageScalars A π (m + 1) n h (parameter A π (m + 1) ^ (m + 1))) • y = s at he
  simpa only [stageParameterSection, map_pow] using he

variable [IsNoetherianRing A]

local instance parameterImagePower_coherent :
    (tensorPower (boundaryLine A π (m + 1) n h) d).IsFinitePresentation :=
  ((boundaryLine_rankOne A π (m + 1) n h).tensorPower d).isFinitePresentation

/-- The adjacent line quotient is the actual first parameter image. -/
def boundaryParameterQuotientIso :
    quotient (stageParameterIdeal A π (m + 1) n h)
      (tensorPower (boundaryLine A π (m + 1) n h) d) (m + 1) ≅
    multiple (stageParameterIdeal A π (m + 1) n h)
      (tensorPower (boundaryLine A π (m + 1) n h) d) :=
  PrincipalScalarCokernel.quotientImageIso
    (stageParameterIdeal A π (m + 1) n h ^ (m + 1))
    (stageParameterIdeal A π (m + 1) n h)
    (tensorPower (boundaryLine A π (m + 1) n h) d)
    (stageParameterSection A π (m + 1) n h)
    (stageParameterIdeal_ideal A π (m + 1) n h)
    (boundaryPower_parameter_annihilator A π hπ m n h d)

/-- The first ideal image is the original preceding-stage tensor line pushed forward. -/
def boundaryParameterImageIso :
    multiple (stageParameterIdeal A π (m + 1) n h)
      (tensorPower (boundaryLine A π (m + 1) n h) d) ≅
    (pushforward (stageRestriction A π m n h)).obj
      (tensorPower (boundaryLine A π m n h) d) :=
  (boundaryParameterQuotientIso A π hπ m n h d).symm ≪≫ boundaryTensorQuotientIso A π m n h d

/-- The quotient-to-image comparison retains multiplication by the actual parameter. -/
@[reassoc] theorem projection_boundaryParameterQuotientIso :
    projection (stageParameterIdeal A π (m + 1) n h)
        (tensorPower (boundaryLine A π (m + 1) n h) d) (m + 1) ≫
      (boundaryParameterQuotientIso A π hπ m n h d).hom ≫
        inclusion (stageParameterIdeal A π (m + 1) n h)
          (tensorPower (boundaryLine A π (m + 1) n h) d) =
    scalarEnd (tensorPower (boundaryLine A π (m + 1) n h) d)
      (stageParameterSection A π (m + 1) n h) :=
  PrincipalScalarCokernel.quotientImageIso_inclusion _ _ _ _ _ _

end FLT.Mazur.PolygonArithmeticStages
