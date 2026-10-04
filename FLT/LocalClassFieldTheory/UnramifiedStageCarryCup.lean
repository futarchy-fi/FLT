/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.CyclicCarryCoefficientCup
public import FLT.LocalClassFieldTheory.FiniteUnitInvariants
public import FLT.LocalClassFieldTheory.UnramifiedCyclicStages
public import FLT.LocalClassFieldTheory.DiscreteOrderExact

/-!
# Uniformizer carry at the actual unramified Frobenius

The positive carry with uniformizer coefficients has negative Tate value at
arithmetic Frobenius. This evaluates the explicit finite-stage cocycle; its
identification with the independently defined fundamental class is separate.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open IsLocalRing groupCohomology

variable (R K C : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field C] [Algebra K C] [Algebra R C] [IsScalarTower R K C]
  [Algebra.IsSeparable K C] [Finite (ResidueField R)] [IsSepClosed C]
  [IsAdicComplete (maximalIdeal R) R]
  {π : R} (hπ : Irreducible π) (n : UnramifiedIndex)

local notation "E" => unramifiedFiniteStage R K C n
local notation "M" => Rep.ofAlgebraAutOnUnits K E
local notation "e" => MulEquiv.symm (unramifiedStageCyclicEquiv R K C n)
local notation "x" => finiteUnitInvariantInclusion K E (Additive.ofMul (fractionUniformizer R K hπ))

/-- The positive finite-stage carry with powers of the actual base uniformizer as coefficients. -/
def unramifiedStageOrdinaryCarry : cocycles₂ M :=
  invariantCoefficientCarry M n.degree e x

/-- The positive carry evaluated at arithmetic Frobenius gives the negative uniformizer class. -/
theorem unramifiedStageCarry_positive_frobenius (hn : 1 < n.degree) :
    tateTwoExtensionMap M (unramifiedStageOrdinaryCarry R K C hπ n) (-2)
      (tateScalarGenerator ℤ Gal(E/K) (unramifiedStageFrobenius R K C n)) =
    -tateInvariantClass M x :=
  invariantCoefficientCarry_positive_generator M n.degree e hn x
    (unramifiedStageFrobenius R K C n) (unramifiedStageCyclicEquiv_frobenius R K C n)

/-- The negative Frobenius bar class maps to the positive uniformizer class. -/
theorem unramifiedStageCarry_negative_frobenius (hn : 1 < n.degree) :
    tateTwoExtensionMap M (unramifiedStageOrdinaryCarry R K C hπ n) (-2)
      (-tateScalarGenerator ℤ Gal(E/K) (unramifiedStageFrobenius R K C n)) =
    tateInvariantClass M x :=
  invariantCoefficientCarry_negative_generator M n.degree e hn x
    (unramifiedStageFrobenius R K C n) (unramifiedStageCyclicEquiv_frobenius R K C n)

end LocalClassFieldTheory
