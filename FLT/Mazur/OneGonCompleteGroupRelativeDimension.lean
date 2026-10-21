/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonCompleteGeneralizedCurve
public import FLT.Mazur.OneGonSmoothingCyclicCartier
public import FLT.Mazur.GeneralizedCurveBaseChange

/-!
# The complete one-gon's entire smooth group has relative dimension one

The existing relative cubic calculation applies to the actual generalized
curve over the complete coefficient ring and to every base change of it.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.OneGonSmoothing
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K]

/-- Relative dimension one holds on the complete one-gon's whole smooth group. -/
instance completeGeneralizedGroup_relativeDimension :
    SmoothOfRelativeDimension 1 (completeGeneralizedCurve K).group.hom :=
  relativeGroup_dimension (PowerSeries.X : PowerSeries K)

/-- Every test over the original complete base retains relative dimension one. -/
theorem completeGeneralizedGroup_baseChange_relativeDimension
    {T : Scheme} (g : T ⟶ Spec (.of (PowerSeries K))) :
    SmoothOfRelativeDimension 1 ((completeGeneralizedCurve K).baseChange g).group.hom :=
  MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1)
    (completeGeneralizedCurve K).group.hom g inferInstance

end FLT.Mazur.OneGonSmoothing
