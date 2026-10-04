/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.RootLocalInvariant
public import FLT.GaloisRepresentation.Extensions.ContinuousCupComparison

/-!
# Artin detection of the actual continuous Kummer cup

The homogeneous continuous cup has the explicit root cup as representative.
Its vanishing is therefore detected by the constructed positive Artin map,
with the invariant's root-ratio-first minus sign proved separately.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open IsLocalRing KummerTheory GaloisRepresentation.Extensions

attribute [local instance] relativeBaseTower unramifiedUnionGalois fieldUnitAction
  unramifiedFieldUnitTopology unramifiedFieldUnitDiscrete
  separableClosureGalois separableClosureUnitTopology separableClosureUnitDiscrete

variable (R K C : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field C] [IsAlgClosed C] [Algebra K C] [Algebra R C] [IsScalarTower R K C]
  [Algebra.IsSeparable K C] [Finite (ResidueField R)] [CharZero C]
  [IsAdicComplete (maximalIdeal R) R]
  (q : ℕ) [Fact q.Prime] (p : ℕ) [Fact p.Prime] [CharP (ResidueField R) p]

local instance kummerCohomologyContinuous : ContinuousSMul Gal(C/K) (RootModule C q) := by
  constructor
  rw [continuous_prod_of_discrete_right]
  exact continuous_root_orbit (K := K)

local instance kummerScalarContinuous : ContinuousSMul (ZMod q) (RootModule C q) :=
  ⟨continuous_of_discreteTopology⟩

/-- Vanishing of the actual homogeneous continuous Kummer cup is positive Artin evaluation. -/
theorem continuousKummerCup_zero_iff_artin
    (χ : ContinuousScalarCharacter Gal(C/K) (ZMod q)) (a : Kˣ) :
    continuousCohomologyCup
      (continuousH1Class (k := ZMod q)
        (continuousRootCocycle a (kummerCarryRoot K C q a) (kummerCarryRoot_pow K C q a))) χ = 0 ↔
      characterArtinValue R K C χ p (Additive.ofMul a) = 0 := by
  rw [continuousCohomologyCup_eq_zero]
  exact kummerCup_coboundary_iff_artin R K C χ p a

/-- The actual homogeneous cup and the injective root invariant detect the same zero class. -/
theorem continuousRootCup_zero_iff_invariant
    (c : ContinuousCocycle Gal(C/K) (RootModule C q))
    (χ : ContinuousScalarCharacter Gal(C/K) (ZMod q)) :
    continuousCohomologyCup (continuousH1Class (k := ZMod q) c) χ = 0 ↔
      rootLocalInvariant R K C q p
        (integralH2Class (k := ℤ) (continuousCup c χ) (continuousCup_isCocycle c χ)) = 0 := by
  rw [continuousCohomologyCup_eq_zero, rootLocalInvariant_eq_zero, integralH2Class_eq_zero]

end LocalClassFieldTheory
