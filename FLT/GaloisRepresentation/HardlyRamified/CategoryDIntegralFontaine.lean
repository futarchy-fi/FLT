/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.AugmentedFontaineBound
public import FLT.GaloisRepresentation.HardlyRamified.CategoryDIntegralModels

/-!
# Integral models of simple category-D objects under Fontaine's bound

Fontaine's local different bound supplies the augmented discriminant estimate,
so a simple category-D object is integrally isomorphic to the constant-three
or cube-root model.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan

/-- Under Fontaine's local bound a simple category-D object is integrally
isomorphic to the constant-three or cube-root model. -/
theorem Simple.integral_model_of_fontaine
    {H : FiniteFlatObject ZInvTwo} (hs : Simple H)
    (hF : FontaineDifferentBoundKilledThree) (hD : InCategoryD H) :
    Nonempty (H.Iso constantThree) ∨ Nonempty (H.Iso muThree) :=
  hs.integral_model_of_discriminantBound hD
    (augmentedDiscriminantBound_of_fontaine hF hs hD)

/-- Fontaine's local bound gives the integral order-three classification
of simple category-D objects. -/
theorem simple_D_three_of_fontaine
    (hF : FontaineDifferentBoundKilledThree)
    (H : FiniteFlatObject ZInvTwo) (hs : Simple H) (hD : InCategoryD H) :
    Nonempty (H.Iso constantThree) ∨ Nonempty (H.Iso muThree) :=
  hs.integral_model_of_fontaine hF hD

end ThreeAdicPlan
