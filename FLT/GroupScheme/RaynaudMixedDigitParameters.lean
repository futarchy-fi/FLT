/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudMixedCharacterParameters
public import FLT.GroupScheme.RaynaudMixedDigitUnit

/-!
# Unit coefficients of actual mixed digit monomials

The original and dual monomial coefficients are constructed from the
actual bases. Their universal product has nonzero residue, so each is a
unit. This includes the all-(p−1) digit vector and its trivial character.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan
open IsLocalRing CharacterAverage

/-- A list of powers has total exponent equal to the sum of its weights. -/
theorem power_list_prod {M : Type*} [Monoid M] (x : M) (ks : List ℕ) :
    (ks.map (fun k ↦ x ^ k)).prod = x ^ ks.sum := by
  induction ks with
  | nil => simp
  | cons k ks ih => simp [ih, pow_add]

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
/-- Both actual mixed digit monomial coefficients are units. -/
theorem FF.exists_mixed_digit_parameter_units (ds : List ℕ) (hds : ∀ d ∈ ds, d < p)
    (hne : Nat.ofDigits p ds ≠ 0) (hq : Nat.ofDigits p ds ≤ Fintype.card Fˣ) :
    ∃ a b : Rˣ,
      (((digitWeights p ds).reverse.map (fun k ↦ χ ^ k)).map
        (X.characterGenerator lift h1 hmul p hdim hlift)).prod =
        (a : R) • X.characterGenerator lift h1 hmul p hdim hlift (χ ^ Nat.ofDigits p ds) ∧
      (((digitWeights p ds).reverse.map (fun k ↦ χ ^ k)).map
        (X.dualCharacterGenerator lift h1 hmul p hdim hlift)).prod =
        (b : R) • X.dualCharacterGenerator lift h1 hmul p hdim hlift (χ ^ Nat.ofDigits p ds) := by
  let cs := (digitWeights p ds).reverse.map (fun k ↦ χ ^ k)
  have hcs : cs ≠ [] := by
    intro hz
    have hz' : digitWeights p ds = [] := List.reverse_eq_nil_iff.mp (List.map_eq_nil_iff.mp hz)
    apply hne
    rw [← digitWeights_sum, hz', List.sum_nil]
  have hp : cs.prod = χ ^ Nat.ofDigits p ds := by
    simp only [cs, power_list_prod, List.sum_reverse, digitWeights_sum]
  obtain ⟨a, b, ha, hb, hab⟩ :=
    X.exists_mixed_character_parameter_product lift h0 h1 hmul hadd p hdim hlift cs hcs
  have hu : IsUnit (a * b) := by
    rw [hab, hp]
    exact isUnit_mixed_digit_constant p χ e he ds hds hne hq
  obtain ⟨hua, hub⟩ := IsUnit.mul_iff.mp hu
  exact ⟨hua.unit, hub.unit, by simpa only [hp, IsUnit.unit_spec] using ha,
    by simpa only [hp, IsUnit.unit_spec] using hb⟩

end ThreeAdicPlan
