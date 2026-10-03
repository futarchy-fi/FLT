/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudCharacterParameterUnits

/-!
# Arithmetic of any actual fundamental power coefficient

The normalized pairing makes the integral power coefficient unique.
Consequently every coefficient derived from the actual coordinate equation
has the already proved complementary p-times-unit product.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan
open IsLocalRing

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

/-- The derived character generator permits cancellation of scalar coefficients. -/
theorem FF.characterGenerator_smul_injective (χ : Fˣ →* Rˣ) :
    Function.Injective (fun a : R ↦ a • X.characterGenerator lift h1 hmul p hdim hlift χ) := by
  intro a b hab
  let φ : HopfAlgebra.CartierDual R X.CoordinateRing :=
    X.dualCharacterGenerator lift h1 hmul p hdim hlift χ
  have hp : φ.ofConv (X.characterGenerator lift h1 hmul p hdim hlift χ) = 1 :=
    X.characterGenerator_pairing lift h1 hmul p hdim hlift χ
  have h := congrArg φ.ofConv hab
  simpa only [map_smul, hp, smul_eq_mul, mul_one] using h

include h0 hadd in
/-- Every actual fundamental power coefficient has a complementary integral coefficient. -/
theorem FF.exists_complementary_prime_coefficient (χ : Fˣ →* Rˣ)
    (e : F →+* ResidueField R) (he : ∀ u : Fˣ, residue R (χ u : R) = e u)
    (a : R) (ha : X.characterGenerator lift h1 hmul p hdim hlift χ ^ p =
      a • X.characterGenerator lift h1 hmul p hdim hlift (χ ^ p)) :
    ∃ (b : R) (u : Rˣ), a * b = (p : R) * u := by
  obtain ⟨a', b, u, ha', _, hab, _⟩ := X.exists_character_prime_parameter_units
    lift h0 h1 hmul hadd p hdim hlift χ e he
  have haa : a = a' := X.characterGenerator_smul_injective lift h1 hmul p hdim hlift
    (χ ^ p) (ha.symm.trans ha')
  exact ⟨b, u, haa ▸ hab⟩

end ThreeAdicPlan
