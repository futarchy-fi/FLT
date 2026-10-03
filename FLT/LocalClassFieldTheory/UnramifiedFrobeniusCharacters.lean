/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.UnramifiedFrobeniusGenerator
public import FLT.LocalClassFieldTheory.RationalCoefficientSequence

/-!
# Frobenius evaluation parametrizes unramified rational-circle characters

Every rational value is realized by a character of the finite stage indexed
by its denominator. Frobenius generation gives uniqueness on the whole quotient.
-/

@[expose] public noncomputable section

universe u

namespace LocalClassFieldTheory

open IsLocalRing

attribute [local instance] rationalCircleCoefficientTopology rationalCircleCoefficientDiscrete

variable (R K C : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field C] [Algebra K C] [Algebra R C] [IsScalarTower R K C]
  [Algebra.IsSeparable K C] [Finite (ResidueField R)] [IsSepClosed C]
  [IsAdicComplete (maximalIdeal R) R]


local notation "U" => maximalUnramified R K C
local notation "Frob" => unramifiedFrobenius R K C

/-- The finite-stage rational-circle character normalized by the positive fraction 1/n. -/
def unramifiedRationalCircleCharacter (n : UnramifiedIndex) :
    Gal(U/K) →ₜ* Multiplicative (AddCircle (1 : ℚ)) :=
  (⟨(zmodToRatCircle n.degree).toMultiplicative, continuous_of_discreteTopology⟩ :
    Multiplicative (ZMod n.degree) →ₜ* Multiplicative (AddCircle (1 : ℚ))).comp
      (unramifiedDegreeCharacter R K C n)

/-- The chosen finite-stage character has positive Frobenius value 1/n. -/
theorem unramifiedRationalCircleCharacter_frobenius (n : UnramifiedIndex) :
    (unramifiedRationalCircleCharacter R K C n Frob).toAdd =
      (↑((1 : ℚ) / n.degree) : AddCircle (1 : ℚ)) := by
  change zmodToRatCircle n.degree ((unramifiedDegreeCharacter R K C n Frob).toAdd) = _
  rw [unramifiedDegreeCharacter_frobenius]
  simpa using zmodToRatCircle_intCast (n.degree : ℕ) 1

/-- Every rational-circle value occurs at arithmetic Frobenius. -/
theorem unramifiedFrobeniusEvaluation_surjective :
    Function.Surjective (fun χ : Gal(U/K) →ₜ* Multiplicative (AddCircle (1 : ℚ)) =>
      (χ Frob).toAdd) := by
  intro x
  induction x using Quotient.inductionOn with | h q =>
    let n : UnramifiedIndex := ⟨⟨q.den, q.den_pos⟩⟩
    let χ := unramifiedRationalCircleCharacter R K C n
    let t : AddCircle (1 : ℚ) →+ AddCircle (1 : ℚ) := q.num • AddMonoidHom.id _
    let t' : Multiplicative (AddCircle (1 : ℚ)) →ₜ* Multiplicative (AddCircle (1 : ℚ)) :=
      ⟨t.toMultiplicative, continuous_of_discreteTopology⟩
    refine ⟨t'.comp χ, ?_⟩
    change q.num • (χ Frob).toAdd = (q : AddCircle (1 : ℚ))
    rw [unramifiedRationalCircleCharacter_frobenius]
    change q.num • (↑((1 : ℚ) / q.den) : AddCircle (1 : ℚ)) = _
    rw [← AddCircle.coe_zsmul]
    congr 1
    simpa only [zsmul_eq_mul, mul_one_div] using q.num_div_den

/-- The constructed unramified quotient has exactly one continuous character per Q/Z value. -/
def unramifiedFrobeniusCharacterEquiv :
    (Gal(U/K) →ₜ* Multiplicative (AddCircle (1 : ℚ))) ≃ AddCircle (1 : ℚ) :=
  Equiv.ofBijective (fun χ => (χ Frob).toAdd)
    ⟨fun χ ψ h => unramifiedCharacter_ext R K C χ ψ h,
      unramifiedFrobeniusEvaluation_surjective R K C⟩

/-- The character equivalence is evaluation at the actual arithmetic Frobenius. -/
theorem unramifiedFrobeniusCharacterEquiv_apply
    (χ : Gal(U/K) →ₜ* Multiplicative (AddCircle (1 : ℚ))) :
    unramifiedFrobeniusCharacterEquiv R K C χ = (χ Frob).toAdd := rfl

end LocalClassFieldTheory
