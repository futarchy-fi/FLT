/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorTensorSequence
public import FLT.Mazur.ClosedLineProjectionFormula

/-!
# The canonical divisor cokernel as a closed pushforward

Tensor exactness and the intrinsic contraction identify the actual cokernel
with the closed pushforward of the restricted divisor line. All comparisons
are global sheaf morphisms, so compatibility of chart transitions is retained.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.FCurve

open ModuleSheafTensor

variable {X : Scheme.{u}} {I : X.IdealSheafData} (hI : EffectiveCartier I)

/-- The canonical section cokernel is the quotient structure module tensored with O(D). -/
def divisorCokernelTensorIso :
    cokernel (divisorSectionMap hI) ≅
      tensor ((pushforward I.subschemeι).obj (structureModule I.subscheme))
        (divisorLineBundle I hI) := by
  let S := (idealQuotientComplex I).map
    (ModuleSheafTensorCurrying.tensoring (divisorLineBundle I hI))
  let e : cokernel S.f ≅ cokernel (divisorSectionMap hI) :=
    cokernel.mapIso S.f (divisorSectionMap hI) (divisorIdealEvaluationIso hI)
      (leftUnitor (divisorLineBundle I hI)) (divisorIdealEvaluation_section hI).symm
  exact e.symm ≪≫ (cokernelIsCokernel S.f).coconePointUniqueUpToIso
    (divisorTensorSequence_shortExact hI).gIsCokernel

/-- The actual canonical divisor cokernel is the closed pushforward of O(D)|D. -/
def divisorCokernelClosedIso :
    cokernel (divisorSectionMap hI) ≅
      (pushforward I.subschemeι).obj
        ((Scheme.Modules.pullback I.subschemeι).obj (divisorLineBundle I hI)) :=
  divisorCokernelTensorIso hI ≪≫
    (ClosedLineProjectionFormula.projectionIso I.subschemeι
      (structureModule I.subscheme) (divisorLineBundle I hI)
      hI.divisorLineBundle_locallyFreeRankOne).symm ≪≫
    (pushforward I.subschemeι).mapIso (leftUnitor _)

end FLT.Mazur.FCurve
