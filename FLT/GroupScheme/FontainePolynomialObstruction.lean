/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.LocalPolynomialObstruction

/-!
# Critical polynomial values obstruct Fontaine's property

A forbidden polynomial value in a finite extension of no larger degree
prevents an embedding of the original field. For an integral generator's
minimal polynomial, the forbidden value is determined by the different
and the largest conjugate displacement.

This file does not construct the perturbed extension. Its remaining input
is an integral element with the critical polynomial value and sufficient
precision in an extension of bounded degree.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan

variable (L E : Type) [Field L] [Algebra ℚ_[3] L] [Algebra ℤ_[3] L]
  [IsScalarTower ℤ_[3] ℚ_[3] L] [FiniteDimensional ℚ_[3] L]
  [Field E] [Algebra ℚ_[3] E] [Algebra ℤ_[3] E]
  [IsScalarTower ℤ_[3] ℚ_[3] E] [FiniteDimensional ℚ_[3] E]

/-- A polynomial value excluded in one field prevents it embedding in an
extension of no larger degree that realizes the value. -/
theorem threeAdicNoEmbeddingOfExcludedValue (f : Polynomial ℤ_[3]) (n : ℕ)
    (hexcluded : ∀ x : ThreeAdicIntegers L,
      IsDiscreteValuationRing.addVal (ThreeAdicIntegers L) (Polynomial.aeval x f) ≠ (n : ℕ∞))
    (hdeg : Module.finrank ℚ_[3] E ≤ Module.finrank ℚ_[3] L)
    (y : ThreeAdicIntegers E)
    (hy : IsDiscreteValuationRing.addVal (ThreeAdicIntegers E) (Polynomial.aeval y f) =
      (n : ℕ∞)) : ¬ Nonempty (L →ₐ[ℚ_[3]] E) := by
  rintro ⟨i⟩
  have hdim : Module.finrank ℚ_[3] L = Module.finrank ℚ_[3] E :=
    le_antisymm
      (LinearMap.finrank_le_finrank_of_injective (f := i.toLinearMap) i.injective) hdeg
  have hsurj : Function.Surjective i :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim
      (f := i.toLinearMap)).mp i.injective
  let e := AlgEquiv.ofBijective i ⟨i.injective, hsurj⟩
  let eInt : ThreeAdicIntegers L ≃ₐ[ℤ_[3]] ThreeAdicIntegers E :=
    (e.restrictScalars ℤ_[3]).mapIntegralClosure
  have heval : eInt (Polynomial.aeval (eInt.symm y) f) = Polynomial.aeval y f := by
    rw [← Polynomial.aeval_algHom_apply, eInt.apply_symm_apply]
  apply hexcluded (eInt.symm y)
  rw [← heval] at hy
  exact (IsDiscreteValuationRing.addValRingEquiv eInt.toRingEquiv _).symm.trans hy

/-- An additive valuation equality gives the precise normalized polynomial order. -/
theorem threeAdicMemValuationIdealOfAddVal (z : ThreeAdicIntegers E) (n : ℕ)
    (hz : IsDiscreteValuationRing.addVal (ThreeAdicIntegers E) z = (n : ℕ∞)) (m : ℚ)
    (hm : m ≤ (n : ℚ) /
      threeAdicIdealOrder E (Ideal.span {(3 : ThreeAdicIntegers E)})) :
    z ∈ threeAdicValuationIdeal E m := by
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, IsDiscreteValuationRing.addVal_zero] at hz
    exact ENat.natCast_ne_top n hz.symm
  rw [threeAdicAddValEqIdealOrder E z hz0, ENat.natCast_inj] at hz
  rw [mem_threeAdicValuationIdeal_iff_order E z hz0 m, normalizedIdealOrder, hz]
  exact hm

/-- A bounded-degree critical-value witness disproves Fontaine's property.
The finite extension and its integral element are the construction inputs. -/
theorem notFontainePropertyOfCriticalValue [IsGalois ℚ_[3] L] (c : ℕ)
    (hbound : ∀ σ : ThreeAdicIntegers L ≃ₐ[ℤ_[3]] ThreeAdicIntegers L, σ ≠ 1 →
      threeAdicIdealOrder L (threeAdicDisplacementIdeal L σ.toAlgHom) ≤ c)
    (hmax : ∃ σ : ThreeAdicIntegers L ≃ₐ[ℤ_[3]] ThreeAdicIntegers L, σ ≠ 1 ∧
      threeAdicIdealOrder L (threeAdicDisplacementIdeal L σ.toAlgHom) = c)
    (hc : 0 < c) (hdeg : Module.finrank ℚ_[3] E ≤ Module.finrank ℚ_[3] L)
    (y : ThreeAdicIntegers E)
    (hy : IsDiscreteValuationRing.addVal (ThreeAdicIntegers E)
      (Polynomial.aeval y (minpoly ℤ_[3] (threeAdicIntegersPowerBasis L).gen)) =
        ((threeAdicIdealOrder L (differentIdeal ℤ_[3] (ThreeAdicIntegers L)) + c - 1 : ℕ) :
          ℕ∞))
    (m : ℚ) (hm : m ≤
      ((threeAdicIdealOrder L (differentIdeal ℤ_[3] (ThreeAdicIntegers L)) + c - 1 : ℕ) : ℚ) /
        threeAdicIdealOrder E (Ideal.span {(3 : ThreeAdicIntegers E)})) :
    ¬ FontaineProperty (ThreeAdicIntegers L) m := by
  apply not_fontaineProperty_of_approximateRoot L E m y
  · exact threeAdicMemValuationIdealOfAddVal E _ _ hy m hm
  · exact threeAdicNoEmbeddingOfExcludedValue L E _ _
      (threeAdicMinpolyAddValNeCritical L c hbound hmax hc) hdeg y hy

end ThreeAdicPlan
