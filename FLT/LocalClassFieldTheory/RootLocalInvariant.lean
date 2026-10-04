/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.RootCoefficientH2
public import FLT.LocalClassFieldTheory.KummerArtinVanishing

/-!
# An injective local invariant on actual root-coefficient H²

Compose the actual coefficient map with the constructed absolute invariant.
The Kummer cup evaluates with the root-ratio-first minus sign, and zero is
detected on the original root-coefficient cohomology group.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open IsLocalRing KummerTheory GaloisRepresentation.Extensions

attribute [local instance] rootCoefficientContinuous relativeBaseTower
  unramifiedUnionGalois fieldUnitAction
  unramifiedFieldUnitTopology unramifiedFieldUnitDiscrete
  separableClosureGalois separableClosureUnitTopology separableClosureUnitDiscrete

variable (R K C : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field C] [IsAlgClosed C] [Algebra K C] [Algebra R C] [IsScalarTower R K C]
  [Algebra.IsSeparable K C] [Finite (ResidueField R)] [CharZero C]
  [IsAdicComplete (maximalIdeal R) R]
  (q : ℕ) [Fact q.Prime] (p : ℕ) [Fact p.Prime] [CharP (ResidueField R) p]

/-- The local invariant on the actual integral continuous H² of root coefficients. -/
def rootLocalInvariant : continuousCohomology ℤ Gal(C/K) (RootModule C q) 2 →+
    AddCircle (1 : ℚ) :=
  (absoluteInvariant R K C p).toAddMonoidHom.comp (rootCoefficientH2 K C q)

/-- Hilbert 90 and the absolute invariant prove injectivity, without a duality premise. -/
theorem rootLocalInvariant_injective : Function.Injective (rootLocalInvariant R K C q p) :=
  (absoluteInvariant R K C p).injective.comp (rootCoefficientH2_injective K C q)

/-- The invariant detects zero in the original root-coefficient cohomology. -/
theorem rootLocalInvariant_eq_zero (x : continuousCohomology ℤ Gal(C/K) (RootModule C q) 2) :
    rootLocalInvariant R K C q p x = 0 ↔ x = 0 :=
  map_eq_zero_iff _ (rootLocalInvariant_injective R K C q p)

/-- The genuine H² root cup evaluates on positive Artin with the root-ratio-first minus sign. -/
theorem rootLocalInvariant_kummer (χ : ContinuousScalarCharacter Gal(C/K) (ZMod q)) (a : Kˣ) :
    rootLocalInvariant R K C q p
      (integralH2Class (k := ℤ)
        (continuousCup (continuousRootCocycle a (kummerCarryRoot K C q a)
          (kummerCarryRoot_pow K C q a)) χ)
        (continuousCup_isCocycle _ _)) =
      -zmodToRatCircle q (characterArtinValue R K C χ p (Additive.ofMul a)) := by
  change absoluteInvariant R K C p (rootCoefficientH2 K C q _) = _
  rw [rootCoefficientH2_class]
  exact canonicalKummer_artin_invariant R K C χ p a

end LocalClassFieldTheory
