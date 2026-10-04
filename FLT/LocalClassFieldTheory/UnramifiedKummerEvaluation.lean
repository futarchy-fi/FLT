/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.UnramifiedParameterInvariant
public import FLT.LocalClassFieldTheory.KummerArtinVanishing

/-!
# Unramified Kummer cup evaluation

The root-valued cup vanishes exactly when the parameter valuation multiplied
by the unramified character's Frobenius value is zero modulo the prime.
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
  {q : ℕ} [Fact q.Prime]
  (χ : ContinuousScalarCharacter Gal(maximalUnramified R K C/K) (ZMod q))
  (p : ℕ) [Fact p.Prime] [CharP (ResidueField R) p]

include p in
/-- An unramified cup vanishes precisely when valuation times Frobenius value vanishes. -/
theorem unramifiedKummer_coboundary_iff (a : Kˣ) :
    ContinuousIsCoboundaryTwo
      (continuousCup (continuousRootCocycle a (kummerCarryRoot K C q a)
        (kummerCarryRoot_pow K C q a)) (inflatedUnramifiedScalarCharacter R K C χ)) ↔
      discreteOrderAdd R K (Additive.ofMul a) • χ.val (unramifiedFrobenius R K C) = 0 := by
  rw [← includedRootTwoCochain_coboundary_iff K C q]
  change ContinuousIsCoboundaryTwo
    (kummerIncludedCup K C q a (inflatedUnramifiedScalarCharacter R K C χ)) ↔ _
  rw [← integralH2Class_eq_zero (k := ℤ) _ (kummerIncludedCup_isCocycle K C q a _)]
  rw [← map_eq_zero_iff _ (absoluteInvariant R K C p).injective,
    kummerCarryCup_class, map_neg]
  have hi : (unramifiedMultiplicativeInflation R K C 2).hom
      (unramifiedParameterCarryClass R K C χ (Additive.ofMul a)) =
      integralH2Class (k := ℤ)
        (cyclicParameterCarry (inflatedUnramifiedScalarCharacter R K C χ)
          (Additive.ofMul (Units.map (algebraMap K C).toMonoidHom a)))
        (cyclicParameterCarry_isCocycle _ _ (kummerCarryParameter_fixed K C a)) :=
    unramifiedParameterCarry_inflation R K C χ (Additive.ofMul a)
  rw [← hi,
    absoluteInvariant_inflation, unramifiedParameterCarry_invariant, neg_eq_zero,
    ← map_zsmul, zmodToRatCircle_eq_zero]

end LocalClassFieldTheory
