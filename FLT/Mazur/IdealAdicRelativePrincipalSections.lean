/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicRelativePrincipalSheaf
public import FLT.Mazur.AffineTildePullbackSectionMap

/-!
# Original sections under principal coefficient sheaf comparison

The principal sheaf comparison sends the actual pullback-unit section to
the tilde section of the original coefficient restriction.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules FLT.Mazur.IdealAdicGradedSections
open scoped ChangeOfRings

universe u

namespace FLT.Mazur.IdealAdicGradedPullback

variable {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsAffine Y]
variable (J : Y.IdealSheafData) (f : X ⟶ Y)

attribute [local irreducible] relativeRestriction relativeMap relativeCoefficientBaseChange

/-- The principal comparison preserves the original restriction of every coefficient section. -/
lemma relativeCoefficientPrincipalPullbackIso_unit (V : X.affineOpens) (r : Γ(X, V.1)) :
    let U : X.affineOpens := ⟨X.basicOpen r, V.2.basicOpen r⟩
    let i : U.1 ⟶ V.1 := homOfLE (X.basicOpen_le r)
    let := closedBaseAlgebra J f V.1
    let := closedBaseAlgebra J f U.1
    ∀ s : relativeChartCoefficient J f V,
      moduleSpecΓFunctor.map (relativeCoefficientPrincipalPullbackIso J f V r).hom
          (AffineTildePullbackSectionMap.unit
            (CommRingCat.ofHom (relativeRestriction J f i).toRingHom)
            (relativeChartCoefficient J f V) s) =
        (relativeChartCoefficientSectionsIso J f U).hom
          (restrictRingHom (J.comap f) U.1 i s) := by
  intro U i _ _ s
  have h := AffineTildePullbackSectionMap.map_unit
    (CommRingCat.ofHom (relativeRestriction J f i).toRingHom)
    (relativeChartCoefficient J f V) (relativeChartCoefficient J f U)
    (relativeCoefficientBaseChange J f V r).hom s
  exact h.trans (congrArg (relativeChartCoefficientSectionsIso J f U).hom
    (relativeCoefficientBaseChange_one_tmul J f V r s))

end FLT.Mazur.IdealAdicGradedPullback
