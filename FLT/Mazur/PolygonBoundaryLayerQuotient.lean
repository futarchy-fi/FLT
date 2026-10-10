/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonBoundaryReductionSequence
public import FLT.Mazur.PolygonStageParameterSections
public import FLT.Mazur.PrincipalScalarCokernel

/-!
# The actual global closed layer of polygon boundary powers

Multiplication by the last parameter power identifies the first parameter
quotient with the kernel sheaf in the original adjacent reduction sequence.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

open FCurve ModuleLineBundleTensorPullback IdealAdicQuotient
open GlobalIdealPower IdealPowerScalarLift

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (R : Type) [CommRing R] [IsNoetherianRing R] (m n : ℕ) (h : 2 ≤ n)

/-- Every actual stage over a Noetherian coefficient ring is locally Noetherian. -/
instance family_locallyNoetherian : IsLocallyNoetherian (family R m n h).left :=
  LocallyOfFiniteType.isLocallyNoetherian (family R m n h).hom

variable (d : ℕ)

local instance boundaryPower_coherent :
    (tensorPower (boundaryLine R (m + 1) n h) d).IsFinitePresentation :=
  ((boundaryLine_rankOne R (m + 1) n h).tensorPower d).isFinitePresentation

/-- The actual closed-fiber quotient is the actual last parameter-power image. -/
def boundaryLayerQuotientIso :
    quotient (stageParameterIdeal R (m + 1) n h)
      (tensorPower (boundaryLine R (m + 1) n h) d) 1 ≅
        (boundaryReductionSequence R m n h d).X₁ :=
  PrincipalScalarCokernel.quotientImageIso
    (stageParameterIdeal R (m + 1) n h ^ 1)
    (stageParameterIdeal R (m + 1) n h ^ (m + 1))
    (tensorPower (boundaryLine R (m + 1) n h) d)
    (stageParameterSection R (m + 1) n h ^ (m + 1))
    (stageParameterPower_ideal R (m + 1) n h (m + 1))
    (fun U s ↦ by simpa only [pow_one] using boundaryPower_last_annihilator R m n h d U s)

/-- The global layer comparison retains multiplication by the original parameter power. -/
@[reassoc] theorem projection_boundaryLayerQuotientIso :
    projection (stageParameterIdeal R (m + 1) n h)
        (tensorPower (boundaryLine R (m + 1) n h) d) 1 ≫
      (boundaryLayerQuotientIso R m n h d).hom ≫
        (boundaryReductionSequence R m n h d).f =
    scalarEnd (tensorPower (boundaryLine R (m + 1) n h) d)
      (stageParameterSection R (m + 1) n h ^ (m + 1)) :=
  PrincipalScalarCokernel.quotientImageIso_inclusion _ _ _ _ _ _

end FLT.Mazur.PolygonInfinitesimalStages
