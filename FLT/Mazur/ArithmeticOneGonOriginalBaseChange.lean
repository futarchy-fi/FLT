/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ArithmeticOneGonRootsBaseChange
public import FLT.Mazur.ArithmeticOneGonBoundaryFiber

/-!
# Original pinched roots are the actual arithmetic boundary pullback

For every coefficient map to a field, the full curve comparison identifies
the original roots with the pullback of the arithmetic subgroup. This includes
nonetale roots when the characteristic divides the order.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.ArithmeticOneGonOriginalBaseChange

open OneGonSmoothing ArithmeticOneGonTorus CharacterSchemeBaseChange
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup

variable (R K : Type) [CommRing R] [Field K] [Algebra R K]
local notation "E" => PolygonGeneralizedCurve.curve K 1 Nat.zero_lt_one
  (OneGonNormalization.normalizationOver K) (OneGonNormalization.nodes K)
  (OneGonGlobalPushout.isPushout K Nat.zero_lt_one)
local notation "F" => GeneralizedEllipticCurve.baseChange (boundaryCurve R) (baseMap R K)
local notation "e" => ArithmeticOneGonFiberTorus.torusIso K (0 : R) (map_zero _)

/-- The whole original pinched curve is the actual coefficient fiber of the boundary model. -/
def curveIso : (E) ≅ (F) :=
  ArithmeticOneGonBoundaryFiber.curveIso K (0 : R) (by simp) (map_zero _)

/-- The full comparison retains the corrected arithmetic fiber group coordinate. -/
theorem curveIso_group :
    (curveIso R K).hom.group = (rootsOfUnityTorusIso K).inv ≫ (e).hom := rfl

/-- The full comparison retains the actual proper coefficient fiber map. -/
theorem curveIso_curve :
    (curveIso R K).hom.curve.left = (zeroParameterFiberIso K (0 : R) (map_zero _)).hom := rfl

attribute [local irreducible] curveIso

variable (n : ℕ) [NeZero n]

/-- The original field roots are the roots in the actual fiber torus coordinate. -/
def fiberCompatibleIso : CompatibleIso (originalRootsOfUnitySubgroup K n)
    (ArithmeticOneGonRootsBaseChange.subgroup R K n) := by
  change CompatibleIso ((E).torusRootsOfUnitySubgroup (rootsOfUnityTorusIso K) n)
    ((F).torusRootsOfUnitySubgroup (e) n)
  exact torusRootsOfUnityCompatibleIso («E» := E) («F» := F)
    (rootsOfUnityTorusIso K) (e) (curveIso R K) (by
    rw [curveIso_group, Iso.hom_inv_id_assoc]) n

/-- The original field roots are the actual pullback of the arithmetic subgroup. -/
def compatibleIso : CompatibleIso (originalRootsOfUnitySubgroup K n)
    ((ArithmeticOneGonRoots.subgroup R n).baseChange (baseMap R K)) :=
  (fiberCompatibleIso R K n).trans (ArithmeticOneGonRootsBaseChange.compatibleIso R K n)

/-- The subgroup map is exactly the original character coefficient comparison. -/
theorem compatibleIso_subgroup :
    (compatibleIso R K n).subgroup.hom =
      (RootsOfUnityArithmeticPullback.comparison R K n).hom := by
  change 𝟙 _ ≫ _ = _
  exact Category.id_comp _

/-- All multiplicities of the original ideal survive the actual arithmetic coefficient pullback. -/
theorem original_ideal :
    ((ArithmeticOneGonRoots.subgroup R n).baseChange (baseMap R K)).ideal =
      (originalRootsOfUnitySubgroup K n).ideal.comap (curveIso R K).inv.curve.left := by
  let h := compatibleIso R K n
  have hi := ideal_transport _ _ h.curve h.subgroup h.compatible
  simpa only [h, compatibleIso, CompatibleIso.trans, ArithmeticOneGonRootsBaseChange.compatibleIso,
    torusRootsOfUnityBaseChangeCompatibleIso, Iso.trans_refl, fiberCompatibleIso,
    torusRootsOfUnityCompatibleIso, id_eq] using hi

/-- Pulling back the arithmetic boundary class gives precisely the original pinched class. -/
theorem level_class :
    ampleCyclicClassesPullback (baseMap R K) n
        (Quotient.mk _ (ArithmeticOneGonOriginalRoots.level n R)) =
      (Quotient.mk _ (ArithmeticOneGonOriginalRoots.originalLevel K n) :
        ampleCyclicClasses (Spec (.of K)) n) :=
  Quotient.sound ⟨(compatibleIso R K n).symm⟩

end FLT.Mazur.ArithmeticOneGonOriginalBaseChange
