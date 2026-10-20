/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonAdicFiniteSubgroup
public import FLT.Mazur.NoetherianFiniteSubgroupCartier
public import FLT.Mazur.WeierstrassSmoothOpenRelativeDimension
public import FLT.Mazur.ArithmeticOneGonSubgroupAmple

/-!
# Cartier and ample effective subgroups on the original adic degeneration

Over Noetherian complete coefficients the constructed finite subgroup is a
relative Cartier divisor on the whole cubic, and its positive rank gives
ampleness for the original complete-base family and its full subgroup ideal.
Cartier cyclicity is a separate remaining condition.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.OneGonAdicCharacterTower

open OneGonSmoothing WeierstrassIntegralChart ArithmeticOneGonGeneralizedCurve

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type} [CommRing R] [IsNoetherianRing R]
  (I : Ideal R) [IsAdicComplete I R] (t : R) (ht : t ∈ I)
  (n : ℕ) [NeZero n] (g : stageSource I (ZMod n) 0 ⟶ stageGroup I t 0)
  [IsClosedImmersion g.hom.hom.hom.left]

/-- The effective full subgroup ideal is relative Cartier on the entire original curve. -/
theorem effectiveFiniteSubgroup_relativeCartier :
    FCurve.RelativeEffectiveCartier (curve t (complementaryFactor_isUnit I t ht)).curve.hom
      (effectiveFiniteSubgroup I t ht n g).ideal := by
  let _ : SmoothOfRelativeDimension 1 (curve t (complementaryFactor_isUnit I t ht)).group.hom :=
    integralSmoothStructure_relativeDimension (equation t)
  exact (effectiveFiniteSubgroup I t ht n g).relativeCartier_of_noetherian_base

/-- The positive-rank effective divisor is ample on the genuine degeneration. -/
theorem effectiveFiniteSubgroup_isAmple : (effectiveFiniteSubgroup I t ht n g).IsAmple :=
  ArithmeticOneGonSubgroupAmple.isAmple t (complementaryFactor_isUnit I t ht) _
    (NeZero.pos n) (effectiveFiniteSubgroup_relativeCartier I t ht n g).1

end FLT.Mazur.OneGonAdicCharacterTower
