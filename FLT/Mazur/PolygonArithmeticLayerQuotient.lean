/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticReductionSequence
public import FLT.Mazur.PolygonArithmeticParameterSections
public import FLT.Mazur.PrincipalScalarCokernel

/-!
# The actual global closed layer of polygon boundary powers

Multiplication by the last parameter power identifies the first parameter
quotient with the kernel sheaf in the original adjacent reduction sequence.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonArithmeticStages

open FCurve ModuleLineBundleTensorPullback IdealAdicQuotient
open GlobalIdealPower IdealPowerScalarLift

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (A : Type) [CommRing A] [IsNoetherianRing A] (π : A) (m n : ℕ) (h : 2 ≤ n)

/-- Every actual stage over a Noetherian coefficient ring is locally Noetherian. -/
instance family_locallyNoetherian : IsLocallyNoetherian (family A π m n h).left :=
  LocallyOfFiniteType.isLocallyNoetherian (family A π m n h).hom

variable [IsDomain A] (hπ : π ≠ 0) (d : ℕ)

local instance boundaryPower_coherent :
    (tensorPower (boundaryLine A π (m + 1) n h) d).IsFinitePresentation :=
  ((boundaryLine_rankOne A π (m + 1) n h).tensorPower d).isFinitePresentation

/-- The actual closed-fiber quotient is the actual last parameter-power image. -/
def boundaryLayerQuotientIso :
    quotient (stageParameterIdeal A π (m + 1) n h)
      (tensorPower (boundaryLine A π (m + 1) n h) d) 1 ≅
        (boundaryReductionSequence A π m n h d).X₁ :=
  PrincipalScalarCokernel.quotientImageIso
    (stageParameterIdeal A π (m + 1) n h ^ 1)
    (stageParameterIdeal A π (m + 1) n h ^ (m + 1))
    (tensorPower (boundaryLine A π (m + 1) n h) d)
    (stageParameterSection A π (m + 1) n h ^ (m + 1))
    (stageParameterPower_ideal A π (m + 1) n h (m + 1))
    (fun U s ↦ by
      simpa only [pow_one] using boundaryPower_last_annihilator A π m n h hπ d U s)

/-- The global layer comparison retains multiplication by the original parameter power. -/
@[reassoc] theorem projection_boundaryLayerQuotientIso :
    projection (stageParameterIdeal A π (m + 1) n h)
        (tensorPower (boundaryLine A π (m + 1) n h) d) 1 ≫
      (boundaryLayerQuotientIso A π m n h hπ d).hom ≫
        (boundaryReductionSequence A π m n h d).f =
    scalarEnd (tensorPower (boundaryLine A π (m + 1) n h) d)
      (stageParameterSection A π (m + 1) n h ^ (m + 1)) :=
  PrincipalScalarCokernel.quotientImageIso_inclusion _ _ _ _ _ _

end FLT.Mazur.PolygonArithmeticStages
