/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudPairedCharacterBases

/-!
# The product of the actual character power parameters

The original and Cartier-dual generators both satisfy power relations.
Their normalized pairing identifies the product of the actual coefficients
with the pairing of their powers. Evaluating that structure constant as p
times a unit is a separate arithmetic calculation.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan
open IsLocalRing

variable {R K F : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [HenselianLocalRing R] [IsSepClosed (ResidueField R)] [Field K] [Algebra R K]
  [CharZero K] [IsFractionRing R K] [Field F] [Finite F] [Fintype Fˣ]
  [Invertible (Fintype.card Fˣ : R)] (X : FF R K) [Module F X.Points]
  (lift : F → ModelHom X X) (h1 : lift 1 = BialgHom.id R X.CoordinateRing)
  (hmul : ∀ a b, lift (a * b) = (lift b).comp (lift a))
  (p : ℕ) [CharP F p] [CharP (ResidueField R) p]
  (hdim : Module.finrank F X.Points = 1)
  (hlift : ∀ a x, genericHom (lift a) x = a • x)

/-- Both coefficients exist and their product is the actual iterated Cartier pairing. -/
theorem FF.exists_character_parameter_product (χ : Fˣ →* Rˣ) (n : ℕ) (hn : n ≠ 0) :
    ∃ a b : R,
      X.characterGenerator lift h1 hmul p hdim hlift χ ^ n =
        a • X.characterGenerator lift h1 hmul p hdim hlift (χ ^ n) ∧
      X.dualCharacterGenerator lift h1 hmul p hdim hlift χ ^ n =
        b • X.dualCharacterGenerator lift h1 hmul p hdim hlift (χ ^ n) ∧
      a * b = (show HopfAlgebra.CartierDual R X.CoordinateRing from
        X.dualCharacterGenerator lift h1 hmul p hdim hlift χ ^ n)
        (X.characterGenerator lift h1 hmul p hdim hlift χ ^ n) := by
  obtain ⟨a, ha⟩ := X.character_power_relation lift h1 hmul p hdim hlift χ n hn
  obtain ⟨b, hb⟩ := X.dual_character_power_relation lift h1 hmul p hdim hlift χ n hn
  refine ⟨a, b, ha, hb, ?_⟩
  rw [ha, hb]
  change a * b = b * (show HopfAlgebra.CartierDual R X.CoordinateRing from
    X.dualCharacterGenerator lift h1 hmul p hdim hlift (χ ^ n)).ofConv
    (a • X.characterGenerator lift h1 hmul p hdim hlift (χ ^ n))
  rw [map_smul]
  change a * b = b * (a * (show HopfAlgebra.CartierDual R X.CoordinateRing from
    X.dualCharacterGenerator lift h1 hmul p hdim hlift (χ ^ n))
    (X.characterGenerator lift h1 hmul p hdim hlift (χ ^ n)))
  rw [X.characterGenerator_pairing, mul_one, mul_comm]

end ThreeAdicPlan
