/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonBoundaryLayerQuotient

/-!
# The first parameter image is the preceding stage line

The affine flatness calculation identifies the annihilator of the parameter
with its last-power image. Thus multiplication by the original parameter
identifies the adjacent quotient line with the first parameter image sheaf.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules

namespace FLT.Mazur.PolygonInfinitesimalStages

open FCurve ModuleLineBundleTensorPullback IdealAdicQuotient
open GlobalIdealPower IdealPowerScalarLift

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (R : Type) [CommRing R] (m n : ℕ) (h : 2 ≤ n) (d : ℕ)

/-- On every affine open, the parameter annihilator is the actual last-power ideal image. -/
theorem boundaryPower_parameter_annihilator
    (U : (family R (m + 1) n h).left.affineOpens)
    (s : Γ(tensorPower (boundaryLine R (m + 1) n h) d, U.1)) :
    (family R (m + 1) n h).left.presheaf.map U.1.leTop.op
        (stageParameterSection R (m + 1) n h) • s = 0 ↔
      s ∈ (stageParameterIdeal R (m + 1) n h ^ (m + 1)).ideal U •
        (⊤ : Submodule Γ((family R (m + 1) n h).left, U.1)
          Γ(tensorPower (boundaryLine R (m + 1) n h) d, U.1)) := by
  let _ := boundaryPowerSections_flat R (m + 1) n h d U.1 U.2
  rw [stageParameterPower_ideal, Submodule.ideal_span_singleton_smul]
  simp only [Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top, true_and]
  have he := flat_parameter_smul_eq_zero_iff R m
    (boundaryPowerSections R (m + 1) n h d U.1) s
  change (family R (m + 1) n h).left.presheaf.map U.1.leTop.op
      (stageScalars R (m + 1) n h (parameter R (m + 1))) • s = 0 ↔
    ∃ y, (family R (m + 1) n h).left.presheaf.map U.1.leTop.op
      (stageScalars R (m + 1) n h (parameter R (m + 1) ^ (m + 1))) • y = s at he
  simpa only [stageParameterSection, map_pow] using he

variable [IsNoetherianRing R]

local instance parameterImagePower_coherent :
    (tensorPower (boundaryLine R (m + 1) n h) d).IsFinitePresentation :=
  ((boundaryLine_rankOne R (m + 1) n h).tensorPower d).isFinitePresentation

/-- The adjacent line quotient is the actual first parameter image. -/
def boundaryParameterQuotientIso :
    quotient (stageParameterIdeal R (m + 1) n h)
      (tensorPower (boundaryLine R (m + 1) n h) d) (m + 1) ≅
    multiple (stageParameterIdeal R (m + 1) n h)
      (tensorPower (boundaryLine R (m + 1) n h) d) :=
  PrincipalScalarCokernel.quotientImageIso
    (stageParameterIdeal R (m + 1) n h ^ (m + 1))
    (stageParameterIdeal R (m + 1) n h)
    (tensorPower (boundaryLine R (m + 1) n h) d)
    (stageParameterSection R (m + 1) n h)
    (stageParameterIdeal_ideal R (m + 1) n h)
    (boundaryPower_parameter_annihilator R m n h d)

/-- The first ideal image is the original preceding-stage tensor line pushed forward. -/
def boundaryParameterImageIso :
    multiple (stageParameterIdeal R (m + 1) n h)
      (tensorPower (boundaryLine R (m + 1) n h) d) ≅
    (pushforward (stageRestriction R m n h)).obj
      (tensorPower (boundaryLine R m n h) d) :=
  (boundaryParameterQuotientIso R m n h d).symm ≪≫ boundaryTensorQuotientIso R m n h d

/-- The quotient-to-image comparison retains multiplication by the actual parameter. -/
@[reassoc] theorem projection_boundaryParameterQuotientIso :
    projection (stageParameterIdeal R (m + 1) n h)
        (tensorPower (boundaryLine R (m + 1) n h) d) (m + 1) ≫
      (boundaryParameterQuotientIso R m n h d).hom ≫
        inclusion (stageParameterIdeal R (m + 1) n h)
          (tensorPower (boundaryLine R (m + 1) n h) d) =
    scalarEnd (tensorPower (boundaryLine R (m + 1) n h) d)
      (stageParameterSection R (m + 1) n h) :=
  PrincipalScalarCokernel.quotientImageIso_inclusion _ _ _ _ _ _

end FLT.Mazur.PolygonInfinitesimalStages
