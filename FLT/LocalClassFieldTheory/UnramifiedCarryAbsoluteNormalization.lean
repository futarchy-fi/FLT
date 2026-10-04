/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.UnramifiedOriginalCarry
public import FLT.LocalClassFieldTheory.AbsoluteFundamentalClass

/-!
# Absolute normalization of the finite carry

Direct inflation of the original finite-stage carry is the absolute class
with positive invariant 1/n.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open IsLocalRing CategoryTheory HomologicalComplex groupCohomology

variable (R K C : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field C] [Algebra K C] [Algebra R C] [IsScalarTower R K C]
  [Algebra.IsSeparable K C] [Finite (ResidueField R)] [IsSepClosed C]
  [IsAdicComplete (maximalIdeal R) R]
  {π : R} (hπ : Irreducible π) (n : UnramifiedIndex)

local notation "U" => maximalUnramified R K C
local notation "E" => unramifiedStage R K C n.degree
local notation "F" => unramifiedFiniteStage R K C n

attribute [local instance] unramifiedOriginalCarryFinite unramifiedOriginalCarryGalois
  unramifiedOriginalCarryTopology unramifiedOriginalCarryDiscrete
  unramifiedUnionGalois fieldUnitAction
  unramifiedFieldUnitTopology unramifiedFieldUnitDiscrete
  separableClosureGalois separableClosureUnitTopology separableClosureUnitDiscrete
  trivialCoefficientAction trivialCoefficientIntComm trivialCoefficientContinuous

local notation "M" => Rep.ofAlgebraAutOnUnits K E
local notation "e" => unramifiedOriginalCarryCoordinate R K C n
local notation "x" => finiteUnitInvariantInclusion K E (Additive.ofMul (fractionUniformizer R K hπ))

/-- The original-stage coordinate restricts to the actual unramified degree character. -/
theorem unramifiedOriginalCarryCoordinate_restrict (g : Gal(C/K)) :
    e (g.restrictNormal E) =
      unramifiedDegreeCharacter R K C n (g.restrictNormal U) := by
  change (unramifiedStageCyclicEquiv R K C n).symm
    (AlgEquiv.autCongr (unramifiedCarryFieldEquiv R K C n) (g.restrictNormal E)) = _
  rw [unramifiedCarry_restriction]
  rfl

/-- Direct and successive carry inflation agree on every cochain. -/
theorem unramifiedOriginalCarry_absolute_complex :
    continuousRestriction (e).toMonoidHom continuous_of_discreteTopology
        (invariantScalarCoefficients M (e).toMonoidHom x) ≫
      continuousRestriction (AlgEquiv.restrictNormalHom E)
        (InfiniteGalois.restrictNormalHom_continuous E)
        (galoisInflationCoefficients K C E) =
    (trivialRestriction (unramifiedDegreeCharacter R K C n) ℤ ≫
      continuousCoefficientMap (unramifiedOrderSection R K C hπ)) ≫
      continuousRestriction (unramifiedRestriction R K C)
        (unramifiedRestriction_continuous R K C)
        (unramifiedMultiplicativeInflationCoefficients R K C) := by
  ext i c : 3
  apply Subtype.ext
  funext g
  have hg : (fun j => e ((g j).restrictNormal E)) =
      (fun j => unramifiedDegreeCharacter R K C n ((g j).restrictNormal U)) :=
    funext fun j => unramifiedOriginalCarryCoordinate_restrict R K C n (g j)
  change (Units.map (E).val.toMonoidHom).toAdditive
    ((c.val (fun j => e ((g j).restrictNormal E))) • (x).val) = _
  rw [map_zsmul, hg]
  apply Additive.toMul.injective
  change _ ^ (c.val (fun j => unramifiedDegreeCharacter R K C n
      ((g j).restrictNormal U))) = Units.map (U).val.toMonoidHom
    (_ ^ (c.val (fun j => unramifiedDegreeCharacter R K C n ((g j).restrictNormal U))))
  rw [map_zpow]
  rfl

/-- Absolute inflation of the finite carry equals inflation of the normalized union carry. -/
theorem unramifiedOriginalContinuousCarry_absolute :
    (galoisMultiplicativeInflation K C E 2).hom
      (unramifiedOriginalContinuousCarry R K C hπ n) =
    (unramifiedMultiplicativeInflation R K C 2).hom
      (unramifiedMultiplicativeCarryClass R K C hπ n) := by
  have h := congrArg (fun f => homologyMap f 2)
    (unramifiedOriginalCarry_absolute_complex R K C hπ n)
  simp only [homologyMap_comp] at h
  exact congrArg (fun f => f.hom
    (integralH2Class (k := ℤ) (cyclicIntegralCarry n.degree)
      (cyclicIntegralCarry_cocycle n.degree))) h

variable [CharZero C] (p : ℕ) [Fact p.Prime] [CharP (ResidueField R) p]

/-- The finite-stage uniformizer carry has positive absolute invariant 1/n. -/
theorem unramifiedOriginalCarry_absolute_invariant :
    absoluteInvariant R K C p ((galoisMultiplicativeInflation K C E 2).hom
      (unramifiedOriginalContinuousCarry R K C hπ n)) =
    (↑((1 : ℚ) / n.degree) : AddCircle (1 : ℚ)) := by
  rw [unramifiedOriginalContinuousCarry_absolute, absoluteInvariant_inflation,
    unramifiedMultiplicativeCarryClass_coordinate]

/-- Absolute inflation identifies the finite carry with the positive absolute fundamental class. -/
theorem unramifiedOriginalCarry_absolute_fundamental :
    (galoisMultiplicativeInflation K C E 2).hom
      (unramifiedOriginalContinuousCarry R K C hπ n) =
    absoluteFundamentalClass R K C p n.degree :=
  (absoluteFundamentalClass_eq_iff R K C p n.degree _).mpr
    (unramifiedOriginalCarry_absolute_invariant R K C hπ n p)

end LocalClassFieldTheory
