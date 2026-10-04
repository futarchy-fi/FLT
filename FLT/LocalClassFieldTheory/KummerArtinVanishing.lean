/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.CanonicalCharacterArtin
public import FLT.LocalClassFieldTheory.KummerParameterCarry
public import FLT.LocalClassFieldTheory.RootCoefficientBoundary

/-!
# Kummer cup vanishing and canonical Artin evaluation

The root-valued cup vanishes exactly when the character kills the Artin image.
The coefficient comparison is proved by Hilbert 90 and root correction.
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
  {q : ℕ} [Fact q.Prime] (χ : ContinuousScalarCharacter Gal(C/K) (ZMod q))
  (p : ℕ) [Fact p.Prime] [CharP (ResidueField R) p]

/-- The canonical local evaluation retains the root-ratio-first minus sign. -/
theorem canonicalKummer_artin_invariant (a : Kˣ) :
    absoluteInvariant R K C p
      (integralH2Class (k := ℤ) (kummerIncludedCup K C q a χ)
        (kummerIncludedCup_isCocycle K C q a χ)) =
      -zmodToRatCircle q (characterArtinValue R K C χ p (Additive.ofMul a)) := by
  rw [kummerCarryCup_class, map_neg]
  exact congrArg Neg.neg (characterArtinValue_carry R K C χ p (Additive.ofMul a))

/-- Vanishing of the original root-valued Kummer cup is detected by Artin evaluation. -/
theorem kummerCup_coboundary_iff_artin (a : Kˣ) :
    ContinuousIsCoboundaryTwo
      (continuousCup (continuousRootCocycle a (kummerCarryRoot K C q a)
        (kummerCarryRoot_pow K C q a)) χ) ↔
      characterArtinValue R K C χ p (Additive.ofMul a) = 0 := by
  rw [← includedRootTwoCochain_coboundary_iff K C q]
  change ContinuousIsCoboundaryTwo (kummerIncludedCup K C q a χ) ↔ _
  rw [← integralH2Class_eq_zero (k := ℤ) _ (kummerIncludedCup_isCocycle K C q a χ)]
  rw [← map_eq_zero_iff _ (absoluteInvariant R K C p).injective,
    canonicalKummer_artin_invariant R K C χ p a, neg_eq_zero, zmodToRatCircle_eq_zero]

end LocalClassFieldTheory
