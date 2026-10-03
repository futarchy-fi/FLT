/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.UnramifiedIntegralH2
public import FLT.LocalClassFieldTheory.IntegralCharacterAdditivity

/-!
# Additive Frobenius coordinates on integral unramified H2

Frobenius evaluation is additive, so the constructed bijection is an
isomorphism of abelian groups. Zero is detected by its rational-circle coordinate.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open IsLocalRing

attribute [local instance] trivialCoefficientAction trivialCoefficientIntComm
  trivialCoefficientContinuous rationalCircleCoefficientTopology rationalCircleCoefficientDiscrete

variable (R K C : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field C] [Algebra K C] [Algebra R C] [IsScalarTower R K C]
  [Algebra.IsSeparable K C] [Finite (ResidueField R)] [IsSepClosed C]
  [IsAdicComplete (maximalIdeal R) R]


local notation "U" => maximalUnramified R K C
local notation "Frob" => unramifiedFrobenius R K C

attribute [local instance] unramifiedH2Galois

/-- Addition of integral H2 classes adds their Frobenius coordinates. -/
theorem unramifiedIntegralH2Equiv_add (x y : continuousCohomology ℤ Gal(U/K) ℤ 2) :
    unramifiedIntegralH2Equiv R K C (x + y) =
      unramifiedIntegralH2Equiv R K C x + unramifiedIntegralH2Equiv R K C y := by
  obtain ⟨χ, rfl⟩ := (integralH2CharacterEquiv Gal(U/K)).surjective x
  obtain ⟨ψ, rfl⟩ := (integralH2CharacterEquiv Gal(U/K)).surjective y
  rw [← integralH2CharacterEquiv_mul, unramifiedIntegralH2Equiv_character,
    unramifiedIntegralH2Equiv_character, unramifiedIntegralH2Equiv_character]
  rfl

/-- Frobenius coordinates are an additive isomorphism for integral unramified H2. -/
def unramifiedIntegralH2AddEquiv : continuousCohomology ℤ Gal(U/K) ℤ 2 ≃+ AddCircle (1 : ℚ) where
  toEquiv := unramifiedIntegralH2Equiv R K C
  map_add' := unramifiedIntegralH2Equiv_add R K C

/-- Vanishing of an integral class is detected by its actual Frobenius coordinate. -/
theorem unramifiedIntegralH2AddEquiv_eq_zero (x : continuousCohomology ℤ Gal(U/K) ℤ 2) :
    unramifiedIntegralH2AddEquiv R K C x = 0 ↔ x = 0 :=
  map_eq_zero_iff _ (unramifiedIntegralH2AddEquiv R K C).injective

/-- Multiplication by an integer acts on Frobenius coordinates by the same integer. -/
theorem unramifiedIntegralH2AddEquiv_zsmul (m : ℤ) (x : continuousCohomology ℤ Gal(U/K) ℤ 2) :
    unramifiedIntegralH2AddEquiv R K C (m • x) = m • unramifiedIntegralH2AddEquiv R K C x :=
  map_zsmul _ _ _

end LocalClassFieldTheory
