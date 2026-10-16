/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXNodeInfinityDenominators
public import FLT.Mazur.WeierstrassModificationXArithmeticNodeOverlap
public import FLT.Mazur.WeierstrassModificationXScaleOneTensor

/-!
# The original arithmetic infinity open equals the initial-node overlap

The full tensor y localization is precisely the common image of both full
initial nodes. The actual coefficient equivalence preserves the original y.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open scoped TensorProduct
namespace FLT.Mazur.WeierstrassModificationX
open PolygonArithmeticStages WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] (π : R) (m : ℕ)
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (ha : IsUnit W.a₁) (h2 : π ∣ W.a₂) (h3 : π ∣ b3) (h4 : π ∣ b4) (h6 : π ∣ b6)
local notation "Q" => Quotient R π m
local notation "q" => algebraMap R Q
local notation "J" => ideal Q (parameter R π m)
local notation "r₀" => polynomialSlopeRoot (W.map q) (q b3) (q b4) (q b6) J
  (arithmeticParameterIdeal_nilpotent π m) (ha.map q)
  (arithmeticCoefficient_mem π m h2) (arithmeticCoefficient_mem π m h3)
  (arithmeticCoefficient_mem π m h4) (arithmeticCoefficient_mem π m h6)
local notation "hr₀" => polynomialSlopeRoot_equation (W.map q) (q b3) (q b4) (q b6) J
  (arithmeticParameterIdeal_nilpotent π m) (ha.map q)
  (arithmeticCoefficient_mem π m h2) (arithmeticCoefficient_mem π m h3)
  (arithmeticCoefficient_mem π m h4) (arithmeticCoefficient_mem π m h6)
local notation "hm₀" => polynomialSlopeRoot_mem (W.map q) (q b3) (q b4) (q b6) J
  (arithmeticParameterIdeal_nilpotent π m) (ha.map q)
  (arithmeticCoefficient_mem π m h2) (arithmeticCoefficient_mem π m h3)
  (arithmeticCoefficient_mem π m h4) (arithmeticCoefficient_mem π m h6)



local notation "A" => Coordinate W s b3 b4 b6
local notation "B" => ExtendedCoordinate W s b3 b4 b6 Q
local notation "L" => PolynomialNodeOpen (W.map q) (q s)
local notation "F₀" => arithmeticInitialNodeChart π m W s b3 b4 b6 ha h2 h3 h4 h6
local notation "G₀" => arithmeticOppositeInitialNodeChart π m W s b3 b4 b6 ha h2 h3 h4 h6
local notation "F" => arithmeticInitialTensorNodeChart π m W s b3 b4 b6 ha h2 h3 h4 h6
local notation "G" => arithmeticOppositeInitialTensorNodeChart π m W s b3 b4 b6 ha h2 h3 h4 h6
local notation "e" => arithmeticInitialTensorIso π m W s b3 b4 b6
local notation "Y" => (1 : Q) ⊗ₜ[R] y W s b3 b4 b6
local notation "y₀" => y (W.map q) (q s) (q b3) (q b4) (q b6)

/-- The actual arithmetic coefficient comparison preserves the complete original y function. -/
theorem arithmeticInitialTensorIso_y_preimage :
    (e).hom ⁻¹' (PrimeSpectrum.basicOpen Y : Set (PrimeSpectrum (Q ⊗[R] A))) =
      (PrimeSpectrum.basicOpen y₀ : Set (PrimeSpectrum B)) := by
  ext z
  change (baseChangeEquiv W s b3 b4 b6 Q Y ∉ z.asIdeal) ↔ y₀ ∉ z.asIdeal
  rw [baseChangeEquiv_tmul, one_smul, y, y, map_mul, coefficientMap_x, coefficientMap_v]

/-- The whole original tensor infinity boundary is the full two-node overlap at every order. -/
theorem arithmeticInitialTensorY_node_intersection :
    (PrimeSpectrum.basicOpen Y : Set (PrimeSpectrum (Q ⊗[R] A))) =
      Set.range F ∩ Set.range G := by
  apply (e).hom.homeomorph.surjective.preimage_injective
  have hp (c : Spec (.of L) ⟶ Spec (.of B)) :
      (e).hom ⁻¹' Set.range (c ≫ (e).hom) = Set.range c := by
    ext z
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨x, (e).hom.homeomorph.injective hx⟩
    · rintro ⟨x, rfl⟩
      exact ⟨x, rfl⟩
  change (e).hom ⁻¹' (PrimeSpectrum.basicOpen Y : Set (PrimeSpectrum (Q ⊗[R] A))) =
    (e).hom ⁻¹' (Set.range (F₀ ≫ (e).hom) ∩ Set.range (G₀ ≫ (e).hom))
  rw [arithmeticInitialTensorIso_y_preimage, Set.preimage_inter, hp, hp]
  exact polynomialInitialY_node_intersection (W.map q) (q s) (q b3) (q b4) (q b6)
    r₀ hr₀ J (arithmeticParameterIdeal_nilpotent π m) hm₀
      (arithmeticCoefficient_mem π m h3)

end FLT.Mazur.WeierstrassModificationX
