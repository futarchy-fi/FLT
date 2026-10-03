/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudCharacterParameterProduct
public import FLT.GroupScheme.RaynaudRankOneConvolution
public import FLT.GroupScheme.RaynaudUniversalCharacterConstant

/-!
# Actual power parameters equal the universal character constant

The rank-one formula and scalar-addition expansion compute the same
convolution power. Pairing with the normalized output generator identifies
the product of the two actual coefficients with the universal scalar.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan
open IsLocalRing WithConv

variable {R K F : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [HenselianLocalRing R] [IsSepClosed (ResidueField R)] [Field K] [Algebra R K]
  [CharZero K] [IsFractionRing R K] [Field F] [Finite F] [Fintype Fˣ]
  [Invertible (Fintype.card Fˣ : R)] (X : FF R K) [Module F X.Points]
  (lift : F → ModelHom X X) (h0 : lift 0 = ModelHom.zero X X)
  (h1 : lift 1 = BialgHom.id R X.CoordinateRing)
  (hmul : ∀ a b, lift (a * b) = (lift b).comp (lift a))
  (hadd : ∀ a b, lift (a + b) = (lift a).add (lift b))
  (p : ℕ) [CharP F p] [CharP (ResidueField R) p]
  (hdim : Module.finrank F X.Points = 1)
  (hlift : ∀ a x, genericHom (lift a) x = a • x)

include h0 hadd in
/-- The actual coefficients have the universal product, derived from scalar addition. -/
theorem FF.exists_universal_character_parameter_product (χ : Fˣ →* Rˣ)
    (n : ℕ) (hn : n ≠ 0) :
    ∃ a b : R,
      X.characterGenerator lift h1 hmul p hdim hlift χ ^ n =
        a • X.characterGenerator lift h1 hmul p hdim hlift (χ ^ n) ∧
      X.dualCharacterGenerator lift h1 hmul p hdim hlift χ ^ n =
        b • X.dualCharacterGenerator lift h1 hmul p hdim hlift (χ ^ n) ∧
      a * b = CharacterAverage.constant χ (χ ^ n) n := by
  obtain ⟨a, b, ha, hb, _⟩ :=
    X.exists_character_parameter_product lift h1 hmul p hdim hlift χ n hn
  refine ⟨a, b, ha, hb, ?_⟩
  have he := X.characterProjector_convPow_eigen lift h0 h1 hmul hadd χ (χ ^ n) n
    (X.characterBasis lift h1 hmul p hdim hlift (χ ^ n) ())
  rw [X.coordinateCharacterProjector_rankOne lift h1 hmul p hdim hlift,
    rankOne_convPow_apply] at he
  change (show HopfAlgebra.CartierDual R X.CoordinateRing from
      X.dualCharacterGenerator lift h1 hmul p hdim hlift χ ^ n)
      (X.characterGenerator lift h1 hmul p hdim hlift (χ ^ n)) •
      X.characterGenerator lift h1 hmul p hdim hlift χ ^ n =
    CharacterAverage.constant χ (χ ^ n) n •
      X.characterGenerator lift h1 hmul p hdim hlift (χ ^ n) at he
  rw [ha, hb] at he
  let φ : HopfAlgebra.CartierDual R X.CoordinateRing :=
    X.dualCharacterGenerator lift h1 hmul p hdim hlift (χ ^ n)
  have hp : φ.ofConv (X.characterGenerator lift h1 hmul p hdim hlift (χ ^ n)) = 1 :=
    X.characterGenerator_pairing lift h1 hmul p hdim hlift (χ ^ n)
  have h := congrArg φ.ofConv he
  change φ.ofConv ((b * φ.ofConv _) • (a • _)) = φ.ofConv (_ • _) at h
  rw [hp, mul_one, map_smul, map_smul, map_smul, hp] at h
  simpa only [smul_eq_mul, mul_one, mul_comm b a] using h

include h0 hadd in
/-- The iterated Cartier pairing itself is the universal structure constant. -/
theorem FF.character_power_pairing_universal (χ : Fˣ →* Rˣ) (n : ℕ) (hn : n ≠ 0) :
    (show HopfAlgebra.CartierDual R X.CoordinateRing from
      X.dualCharacterGenerator lift h1 hmul p hdim hlift χ ^ n)
      (X.characterGenerator lift h1 hmul p hdim hlift χ ^ n) =
        CharacterAverage.constant χ (χ ^ n) n := by
  obtain ⟨a, b, ha, hb, hab⟩ := X.exists_universal_character_parameter_product
    lift h0 h1 hmul hadd p hdim hlift χ n hn
  rw [ha, hb]
  change b * (show HopfAlgebra.CartierDual R X.CoordinateRing from
    X.dualCharacterGenerator lift h1 hmul p hdim hlift (χ ^ n)).ofConv
      (a • X.characterGenerator lift h1 hmul p hdim hlift (χ ^ n)) = _
  rw [map_smul]
  change b * (a * _) = _
  rw [X.characterGenerator_pairing, mul_one, mul_comm, hab]

end ThreeAdicPlan
