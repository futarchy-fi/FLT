/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ToricFiniteSubgroupRootsCompatibility
public import FLT.Mazur.ArithmeticOneGonOriginalBaseChange

/-!
# Every original one-gon subgroup has an actual arithmetic boundary source

The classification of arbitrary finite toric subgroups upgrades the original
roots comparison to every original subgroup, including nonetale ones. The
arithmetic source is still a boundary family; no extension onto a smoothing is
asserted here.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.ArithmeticOneGonArbitrarySubgroupPullback

open OneGonSmoothing GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
open CharacterSchemeBaseChange

variable (R K : Type) [CommRing R] [Field K] [Algebra R K]
local notation "E" => PolygonGeneralizedCurve.curve K 1 Nat.zero_lt_one
  (OneGonNormalization.normalizationOver K) (OneGonNormalization.nodes K)
  (OneGonGlobalPushout.isPushout K Nat.zero_lt_one)

variable {n : ℕ} [NeZero n]
  (H : (PolygonGeneralizedCurve.curve K 1 Nat.zero_lt_one
    (OneGonNormalization.normalizationOver K) (OneGonNormalization.nodes K)
    (OneGonGlobalPushout.isPushout K Nat.zero_lt_one)).FiniteSubgroup n)

attribute [local irreducible] ToricFiniteSubgroupRootsClassification.compatibleIso
  ArithmeticOneGonOriginalBaseChange.compatibleIso

/-- Every original subgroup, not only a previously specified roots subgroup, has this source. -/
def compatibleIso : CompatibleIso H
    ((ArithmeticOneGonRoots.subgroup R n).baseChange (baseMap R K)) :=
  (ToricFiniteSubgroupRootsClassification.compatibleIso H (rootsOfUnityTorusIso K)).trans
    (ArithmeticOneGonOriginalBaseChange.compatibleIso R K n)

attribute [local irreducible] compatibleIso

/-- The entire original ideal is retained on the actual arithmetic coefficient fiber. -/
theorem original_ideal :
    ((ArithmeticOneGonRoots.subgroup R n).baseChange (baseMap R K)).ideal =
      H.ideal.comap (compatibleIso R K H).curve.inv.curve.left :=
  ideal_transport _ _ (compatibleIso R K H).curve (compatibleIso R K H).subgroup
    (compatibleIso R K H).compatible

/-- Every original finite subgroup on this one-gon is Cartier cyclic. -/
theorem original_isCyclic : H.IsCyclic :=
  (ToricFiniteSubgroupRootsClassification.compatibleIso H
    (rootsOfUnityTorusIso K)).isCyclic_iff.mpr (originalRootsOfUnitySubgroup_isCyclic K n)

/-- The whole original subgroup divisor is ample. -/
theorem original_isAmple : H.IsAmple :=
  (ToricFiniteSubgroupRootsClassification.compatibleIso H
    (rootsOfUnityTorusIso K)).isAmple_iff.mpr (originalRootsOfUnitySubgroup_isAmple K n)

/-- The actual arithmetic boundary class pulls back to any original one-gon subgroup class. -/
theorem level_class (hc : H.IsCyclic) (ha : H.IsAmple) :
    ampleCyclicClassesPullback (baseMap R K) n
        (Quotient.mk _ (ArithmeticOneGonOriginalRoots.level n R)) =
      (Quotient.mk _ ⟨⟨E, H⟩, hc, ha⟩ : ampleCyclicClasses (Spec (.of K)) n) := by
  apply (ArithmeticOneGonOriginalBaseChange.level_class R K n).trans
  exact Quotient.sound ⟨(ToricFiniteSubgroupRootsClassification.compatibleIso H
    (rootsOfUnityTorusIso K)).symm⟩

end FLT.Mazur.ArithmeticOneGonArbitrarySubgroupPullback
