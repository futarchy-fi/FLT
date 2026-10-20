/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonRootsOfUnitySubgroup
public import FLT.Mazur.GeneralizedCurveAmpleSubgroup
public import FLT.Mazur.AmplePositiveTensorPower

/-!
# Ample identity thickenings on the original pinched one-gon

The one-component polygon marking is its identity divisor. Its existing cubic
embedding proves ampleness, and every positive identity thickening inherits
ampleness of its actual divisor line bundle.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry MonObj MonoidalCategory

namespace FLT.Mazur.OneGonSmoothing

open GeneralizedEllipticCurve FCurve

variable (K : Type) [Field K]
local notation "E" => PolygonGeneralizedCurve.curve K 1 Nat.zero_lt_one
  (OneGonNormalization.normalizationOver K) (OneGonNormalization.nodes K)
  (OneGonGlobalPushout.isPushout K Nat.zero_lt_one)
local notation "H" => PolygonFiniteSubgroup.subgroup K 1
  (OneGonNormalization.normalizationOver K) Nat.zero_lt_one (OneGonNormalization.nodes K)
  (OneGonGlobalPushout.isPushout K Nat.zero_lt_one)

/-- The singleton polygon marking is exactly the identity divisor of the original curve. -/
theorem originalOneGon_identityIdeal : (H).ideal = (E).identitySection.left.ker := by
  have h := (PolygonCartierGenerator.isCartierGenerator K 1
    (OneGonNormalization.normalizationOver K) Nat.zero_lt_one (OneGonNormalization.nodes K)
    (OneGonGlobalPushout.isPushout K Nat.zero_lt_one)).2.2
  simpa only [Fin.prod_univ_one, Fin.val_zero, pow_zero, FiniteSubgroup.curveMap,
    ← Category.assoc, one_comp, identitySection, ← one_eq_one, IsMonHom.one_hom] using h

/-- The original singular curve's identity divisor is effective Cartier. -/
theorem originalOneGon_identityCartier : EffectiveCartier (E).identitySection.left.ker := by
  rw [← originalOneGon_identityIdeal K]
  exact (PolygonFiniteSubgroup.relativeCartier K 1 (OneGonNormalization.normalizationOver K)
    Nat.zero_lt_one (OneGonNormalization.nodes K)
    (OneGonGlobalPushout.isPushout K Nat.zero_lt_one)).1

/-- The actual identity divisor line is relatively ample on the original pinched curve. -/
theorem originalOneGon_identityAmple : RelativeAmple (E).curve.hom
    (divisorLineBundle (E).identitySection.left.ker (originalOneGon_identityCartier K)) := by
  obtain ⟨hI, ha⟩ := PolygonFiniteSubgroup.isAmple K 1
    (OneGonNormalization.normalizationOver K) Nat.zero_lt_one (OneGonNormalization.nodes K)
    (OneGonGlobalPushout.isPushout K Nat.zero_lt_one)
  exact ha.of_iso (divisorLineBundleEqIso (originalOneGon_identityIdeal K).symm
    (originalOneGon_identityCartier K) hI)

/-- Every positive thickening of the original identity has an ample divisor line. -/
theorem originalOneGon_identityPowerAmple (n : ℕ) (hn : 0 < n) : RelativeAmple (E).curve.hom
    (divisorLineBundle ((E).identitySection.left.ker ^ n)
      ((originalOneGon_identityCartier K).pow n)) :=
  (originalOneGon_identityAmple K).divisorPower (originalOneGon_identityCartier K) hn

end FLT.Mazur.OneGonSmoothing
