/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonAdicCharacterClosedImmersion
public import FLT.Mazur.ArithmeticOneGonGeneralizedCurve
public import FLT.Mazur.GeneralizedCurveSubgroupIdeal
public import FLT.Mazur.RootsOfUnityScheme

/-!
# Finite locally free subgroups on the actual complete-base degeneration

A closed initial roots embedding extends to a finite locally free subgroup
of rank n on the original nonconstant arithmetic cubic. Adic completeness
supplies the complementary discriminant unit; no constant-family replacement
or assumption of the extended subgroup is used.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.OneGonAdicCharacterTower

open OneGonSmoothing WeierstrassIntegralChart CharacterSchemeBaseChange
open ArithmeticOneGonGeneralizedCurve

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
  (t : R) (ht : t ∈ I)

include ht in
/-- The complementary discriminant factor is invertible over the original complete base. -/
theorem complementaryFactor_isUnit : IsUnit (1 + 432 * t) := by
  have h := (Ideal.mem_jacobson_bot.mp (IsAdicComplete.le_jacobson_bot I ht)) (432 : R)
  simpa only [mul_comm, add_comm] using h

variable (n : ℕ) [NeZero n]
  (g : stageSource I (ZMod n) 0 ⟶ stageGroup I t 0)
  [IsClosedImmersion g.hom.hom.hom.left]

/-- The constructed subgroup on the whole original smoothing, of exact rank n. -/
def effectiveFiniteSubgroup :
    (curve t (complementaryFactor_isUnit I t ht)).FiniteSubgroup n where
  carrier := model R (ZMod n)
  inclusion := effectiveSmoothOver I t ht g
  closed := effectiveCharacterHom_isClosedImmersion I t ht g
  degree := RootsOfUnityScheme.degree R n

/-- Its structure map has the proved finite locally free rank, in every characteristic. -/
theorem effectiveFiniteSubgroup_degree :
    FCurve.FiniteLocallyFreeDegree (effectiveFiniteSubgroup I t ht n g).carrier.hom n :=
  (effectiveFiniteSubgroup I t ht n g).degree

/-- Its original whole-curve embedding retains the constructed effective smooth map. -/
theorem effectiveFiniteSubgroup_curveMap :
    (effectiveFiniteSubgroup I t ht n g).curveMap.left =
      effectiveSmooth I t ht g ≫ (integralSmoothOpen (equation t)).ι := by
  change (effectiveSmoothOver I t ht g ≫
    (curve t (complementaryFactor_isUnit I t ht)).inclusion).left = _
  rw [curve_inclusion]
  rfl

/-- The full original ideal is the kernel of the constructed effective map into the cubic. -/
theorem effectiveFiniteSubgroup_ideal :
    (effectiveFiniteSubgroup I t ht n g).ideal =
      (effectiveAffine I t ht g ≫ integralCurveChart (equation t) 1).ker := by
  rw [GeneralizedEllipticCurve.FiniteSubgroup.ideal, effectiveFiniteSubgroup_curveMap,
    effectiveSmooth_inclusion]

end FLT.Mazur.OneGonAdicCharacterTower
