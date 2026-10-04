/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.UnramifiedKummerEvaluation
public import FLT.LocalClassFieldTheory.DiscreteOrderUnitPowers

/-!
# The independent unit annihilator for prime root coefficients

All characters of the actual unramified quotient annihilate a Kummer class
exactly when its parameter has an integral-unit representative modulo powers.
The normalized degree character detects the reverse inclusion.
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
  (q : ℕ) [Fact q.Prime]

local notation "U" => maximalUnramified R K C
local notation "idx" => (UnramifiedIndex.mk (Subtype.mk q (Nat.Prime.pos Fact.out)))

/-- The constructed degree-q character in scalar notation on the unramified quotient. -/
def unramifiedScalarDegreeCharacter : ContinuousScalarCharacter Gal(U/K) (ZMod q) :=
  ⟨⟨fun g => (unramifiedDegreeCharacter R K C idx g).toAdd,
    (unramifiedDegreeCharacter R K C idx).continuous⟩,
    fun g h => congrArg Multiplicative.toAdd (map_mul (unramifiedDegreeCharacter R K C idx) g h)⟩

omit [CharZero C] in
/-- The detecting scalar character takes arithmetic Frobenius to one. -/
theorem unramifiedScalarDegreeCharacter_frobenius :
    (unramifiedScalarDegreeCharacter R K C q).val (unramifiedFrobenius R K C) = 1 :=
  congrArg Multiplicative.toAdd (unramifiedDegreeCharacter_frobenius R K C idx)

variable (p : ℕ) [Fact p.Prime] [CharP (ResidueField R) p]

include p in
/-- Vanishing against all unramified characters is zero order modulo q. -/
theorem unramifiedKummer_annihilator_iff_order (a : Kˣ) :
    (∀ χ : ContinuousScalarCharacter Gal(U/K) (ZMod q),
      ContinuousIsCoboundaryTwo
        (continuousCup (continuousRootCocycle a (kummerCarryRoot K C q a)
          (kummerCarryRoot_pow K C q a)) (inflatedUnramifiedScalarCharacter R K C χ))) ↔
      (discreteOrderAdd R K (Additive.ofMul a) : ZMod q) = 0 := by
  constructor
  · intro h
    have he := (unramifiedKummer_coboundary_iff R K C
      (unramifiedScalarDegreeCharacter R K C q) p a).mp
        (h (unramifiedScalarDegreeCharacter R K C q))
    rw [unramifiedScalarDegreeCharacter_frobenius] at he
    simpa using he
  · intro ha χ
    apply (unramifiedKummer_coboundary_iff R K C χ p a).mpr
    simp [zsmul_eq_mul, ha]

include p in
/-- Both inclusions of the prime-root unit annihilator, using independent unit representatives. -/
theorem unramifiedKummer_annihilator_iff_unit (a : Kˣ) :
    (∀ χ : ContinuousScalarCharacter Gal(U/K) (ZMod q),
      ContinuousIsCoboundaryTwo
        (continuousCup (continuousRootCocycle a (kummerCarryRoot K C q a)
          (kummerCarryRoot_pow K C q a)) (inflatedUnramifiedScalarCharacter R K C χ))) ↔
      ∃ (b : Kˣ) (u : Rˣ), a = b ^ q * Units.map (algebraMap R K) u := by
  rw [unramifiedKummer_annihilator_iff_order R K C q p,
    ZMod.intCast_zmod_eq_zero_iff_dvd, discreteOrder_dvd_iff_unit_power]

end LocalClassFieldTheory
