/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudResidueCharacterUnits
public import FLT.GroupScheme.RaynaudUniversalParameterProduct

/-!
# Derived arithmetic of the actual character power coefficients

The original and dual integral coefficients are constructed from their
proved bases. Their universal product calculation gives the fundamental
p-times-unit identity and unit coefficients for positive powers below p.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan
open IsLocalRing CharacterAverage

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
  (χ : Fˣ →* Rˣ) (e : F →+* ResidueField R)
  (he : ∀ u : Fˣ, residue R (χ u : R) = e u)

include h0 hadd he in
/-- The actual fundamental coefficients have product p times a proved unit. -/
theorem FF.exists_character_prime_parameter_units :
    ∃ (a b : R) (u : Rˣ),
      X.characterGenerator lift h1 hmul p hdim hlift χ ^ p =
        a • X.characterGenerator lift h1 hmul p hdim hlift (χ ^ p) ∧
      X.dualCharacterGenerator lift h1 hmul p hdim hlift χ ^ p =
        b • X.dualCharacterGenerator lift h1 hmul p hdim hlift (χ ^ p) ∧
      a * b = (p : R) * u ∧ residue R (u : R) = -1 := by
  obtain ⟨a, b, ha, hb, hab⟩ := X.exists_universal_character_parameter_product
    lift h0 h1 hmul hadd p hdim hlift χ p (CharP.char_is_prime F p).ne_zero
  obtain ⟨u, hu, hr⟩ := constant_eq_prime_mul_unit p χ e he
  exact ⟨a, b, u, ha, hb, hab.trans hu, hr⟩

include h0 hadd he in
/-- Below p, both actual single-character power coefficients are units. -/
theorem FF.exists_character_digit_parameter_units (n : ℕ) (hn : n ≠ 0) (hnp : n < p) :
    ∃ a b : Rˣ,
      X.characterGenerator lift h1 hmul p hdim hlift χ ^ n =
        (a : R) • X.characterGenerator lift h1 hmul p hdim hlift (χ ^ n) ∧
      X.dualCharacterGenerator lift h1 hmul p hdim hlift χ ^ n =
        (b : R) • X.dualCharacterGenerator lift h1 hmul p hdim hlift (χ ^ n) := by
  obtain ⟨a, b, ha, hb, hab⟩ := X.exists_universal_character_parameter_product
    lift h0 h1 hmul hadd p hdim hlift χ n hn
  have hu : IsUnit (a * b) := hab ▸ isUnit_digit_constant p χ e he n hn hnp
  obtain ⟨hua, hub⟩ := IsUnit.mul_iff.mp hu
  exact ⟨hua.unit, hub.unit, by simpa using ha, by simpa using hb⟩

end ThreeAdicPlan
