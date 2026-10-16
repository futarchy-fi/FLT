/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonSmoothingNodeBasicOpen

/-!
# Polynomial numerators on the explicit original node neighborhood

Every function has an original two-variable numerator after multiplying by a
power of (1-x)(1-y). Two functions have a common denominator without changing
any lower polynomial coefficient or discarding smoothing-parameter nilpotents.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.PolygonSmoothing
variable {R : Type*} [CommRing R] (t : R)
local notation "A" => Localization.Away (nodeMarkingDenominator t)

/-- The explicit denominator before imposing the original smoothing relation. -/
def nodeMarkingDenominatorPolynomial : MvPolynomial (Fin 2) R :=
  (1 - MvPolynomial.X 0) * (1 - MvPolynomial.X 1)

/-- The polynomial denominator retains precisely the original chart denominator. -/
theorem nodeMarkingDenominatorPolynomial_mk :
    Ideal.Quotient.mk (relationIdeal t) (nodeMarkingDenominatorPolynomial (R := R)) =
      nodeMarkingDenominator t := by
  simp only [nodeMarkingDenominatorPolynomial, map_mul, map_sub, map_one,
    nodeMarkingDenominator, leftCoordinate, rightCoordinate]

/-- The actual polynomial evaluation into the full explicit node localization. -/
def nodeLocalizedPolynomialMap : MvPolynomial (Fin 2) R →+* A :=
  (algebraMap (ChartRing t) (A)).comp (Ideal.Quotient.mk (relationIdeal t))

/-- The same polynomial denominator becomes its original localization image. -/
theorem nodeLocalizedPolynomialMap_denominator :
    nodeLocalizedPolynomialMap t (nodeMarkingDenominatorPolynomial (R := R)) =
      algebraMap (ChartRing t) (A) (nodeMarkingDenominator t) := by
  exact congrArg (algebraMap (ChartRing t) (A)) (nodeMarkingDenominatorPolynomial_mk t)

/-- Every localized function has a numerator in the original two node variables. -/
theorem nodeLocalizedPolynomial_exists (s : A) :
    ∃ (r : ℕ) (p : MvPolynomial (Fin 2) R),
      s * algebraMap (ChartRing t) (A) (nodeMarkingDenominator t) ^ r =
        nodeLocalizedPolynomialMap t p := by
  obtain ⟨r, a, ha⟩ := IsLocalization.Away.surj (nodeMarkingDenominator t) s
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  exact ⟨r, p, ha⟩

/-- Both retained functions can be expanded using one unchanged polynomial denominator. -/
theorem nodeLocalizedPolynomial_pair (s v : A) :
    ∃ (r : ℕ) (p q : MvPolynomial (Fin 2) R),
      s * algebraMap (ChartRing t) (A) (nodeMarkingDenominator t) ^ r =
          nodeLocalizedPolynomialMap t p ∧
        v * algebraMap (ChartRing t) (A) (nodeMarkingDenominator t) ^ r =
          nodeLocalizedPolynomialMap t q := by
  obtain ⟨a, p, hp⟩ := nodeLocalizedPolynomial_exists t s
  obtain ⟨b, q, hq⟩ := nodeLocalizedPolynomial_exists t v
  refine ⟨a + b, p * nodeMarkingDenominatorPolynomial ^ b,
    q * nodeMarkingDenominatorPolynomial ^ a, ?_, ?_⟩
  · rw [pow_add, ← mul_assoc, hp, map_mul, map_pow,
      nodeLocalizedPolynomialMap_denominator]
  · rw [Nat.add_comm, pow_add, ← mul_assoc, hq, map_mul, map_pow,
      nodeLocalizedPolynomialMap_denominator]

end FLT.Mazur.PolygonSmoothing
