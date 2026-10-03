/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.DiscreteOrder

/-!
# Exactness of integral units, fraction-field units, and order

Uniformizer factorization identifies the kernel of order with the actual
integral units and proves order surjective.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

variable (S L : Type*) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Field L] [Algebra S L] [IsFractionRing S L]

/-- A uniformizer, regarded as an invertible fraction-field element. -/
def fractionUniformizer {π : S} (hπ : Irreducible π) : Lˣ :=
  Units.mk0 (algebraMap S L π) (by
    simpa using (IsFractionRing.injective S L).ne hπ.ne_zero)

/-- The fraction-field uniformizer has classical order one. -/
@[simp] theorem discreteOrder_fractionUniformizer {π : S} (hπ : Irreducible π) :
    discreteOrder S L (fractionUniformizer S L hπ) = Multiplicative.ofAdd 1 :=
  discreteOrder_uniformizer S L hπ

/-- Every fraction-field unit is an integral unit times an integer uniformizer power. -/
theorem exists_unit_mul_fractionUniformizer_zpow {π : S} (hπ : Irreducible π) (x : Lˣ) :
    ∃ (u : Sˣ) (n : ℤ), x = Units.map (algebraMap S L) u * fractionUniformizer S L hπ ^ n := by
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible
    hπ (Units.ne_zero x)
  refine ⟨u, n, Units.ext ?_⟩
  simpa [fractionUniformizer, Units.smul_def, Algebra.smul_def] using hu

/-- The kernel of order is the image of the integral units. -/
theorem discreteOrder_eq_one_iff (x : Lˣ) :
    discreteOrder S L x = 1 ↔ ∃ u : Sˣ, Units.map (algebraMap S L) u = x := by
  constructor
  · intro hx
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible S
    obtain ⟨u, n, rfl⟩ := exists_unit_mul_fractionUniformizer_zpow S L hπ x
    have hn : n = 0 := by simpa using hx
    exact ⟨u, by simp [hn]⟩
  · rintro ⟨u, rfl⟩
    exact discreteOrder_unit S L u

/-- Every integer occurs as the order of a fraction-field unit. -/
theorem discreteOrder_surjective : Function.Surjective (discreteOrder S L) := by
  intro n
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible S
  refine ⟨fractionUniformizer S L hπ ^ n.toAdd, ?_⟩
  rw [map_zpow, discreteOrder_fractionUniformizer]
  apply Multiplicative.toAdd.injective
  change n.toAdd • (1 : ℤ) = n.toAdd
  simp

end LocalClassFieldTheory
