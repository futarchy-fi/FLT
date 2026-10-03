/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudCharacterPowers
public import FLT.GroupScheme.RaynaudFundamentalCharacter

/-!
# Cyclic equations for the actual fundamental character generators

Choose generators only from the derived rank-one summands. Frobenius
periodicity and the power-character calculation give cyclic p-power equations.
The dual parameter identities and generation of the full algebra are separate
obligations.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan
open IsLocalRing

variable {R K F : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [HenselianLocalRing R] [IsSepClosed (ResidueField R)] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] [Field F] [Fintype F] [DecidableEq F]
  (X : FF R K) [Module F X.Points]
  (p : ℕ) [CharP F p] [CharP (ResidueField R) p]
  (lift : F → ModelHom X X) (h1 : lift 1 = BialgHom.id R X.CoordinateRing)
  (hmul : ∀ a b, lift (a * b) = (lift b).comp (lift a))
  (hdim : Module.finrank F X.Points = 1)
  (hlift : ∀ a x, genericHom (lift a) x = a • x)

/-- An actual generator of the i-th Frobenius character summand. -/
def FF.fundamentalCoordinate (e : F →+* ResidueField R) (i : ℕ) : X.CoordinateRing :=
  X.characterGenerator lift h1 hmul p hdim hlift (fundamentalCharacter p e ^ (p ^ i))

/-- These generators are nonzero in the actual coordinate ring. -/
theorem FF.fundamentalCoordinate_ne_zero (e : F →+* ResidueField R) (i : ℕ) :
    X.fundamentalCoordinate p lift h1 hmul hdim hlift e i ≠ 0 := by
  intro h
  apply (X.characterBasis lift h1 hmul p hdim hlift
    (fundamentalCharacter p e ^ (p ^ i))).ne_zero ()
  apply Subtype.ext
  apply Subtype.ext
  exact h

/-- Each generator's p-th power is an integral multiple of the next generator. -/
theorem FF.fundamentalCoordinate_power (e : F →+* ResidueField R) (i : ℕ) :
    ∃ a : R, (X.fundamentalCoordinate p lift h1 hmul hdim hlift e i) ^ p =
      a • X.fundamentalCoordinate p lift h1 hmul hdim hlift e (i + 1) := by
  have hp : p ≠ 0 := (CharP.char_is_prime F p).ne_zero
  simpa only [FF.fundamentalCoordinate, ← pow_mul, ← pow_succ] using
    X.character_power_relation lift h1 hmul p hdim hlift
      (fundamentalCharacter p e ^ (p ^ i)) p hp

/-- The actual generators repeat after the finite-field Frobenius period. -/
theorem FF.fundamentalCoordinate_periodic (e : F →+* ResidueField R) (r : ℕ)
    (hr : Fintype.card F = p ^ r) (i : ℕ) :
    X.fundamentalCoordinate p lift h1 hmul hdim hlift e (i + r) =
      X.fundamentalCoordinate p lift h1 hmul hdim hlift e i := by
  have hχ : fundamentalCharacter p e ^ (p ^ (i + r)) =
      fundamentalCharacter p e ^ (p ^ i) := by
    rw [pow_add, mul_comm (p ^ i), pow_mul, fundamentalCharacter_periodic p e r hr]
  simp only [FF.fundamentalCoordinate, hχ]

include lift h1 hmul hdim hlift in
omit [DecidableEq F] in
/-- Cyclic nonzero coordinates and coefficients exist without presentation data. -/
theorem FF.exists_cyclic_character_equations :
    ∃ (r : ℕ+) (x : ℕ → X.CoordinateRing) (a : ℕ → R),
      Fintype.card F = p ^ (r : ℕ) ∧
      (∀ i, x i ≠ 0) ∧ (∀ i, x (i + r) = x i) ∧
      (∀ i, x i ^ p = a i • x (i + 1)) := by
  classical
  obtain ⟨r, _, hr⟩ := FiniteField.card F p
  obtain ⟨e⟩ := exists_scalar_residue_embedding (R := R) (F := F) p
  choose a ha using X.fundamentalCoordinate_power p lift h1 hmul hdim hlift e
  exact ⟨r, X.fundamentalCoordinate p lift h1 hmul hdim hlift e, a, hr,
    X.fundamentalCoordinate_ne_zero p lift h1 hmul hdim hlift e,
    X.fundamentalCoordinate_periodic p lift h1 hmul hdim hlift e r hr, ha⟩

end ThreeAdicPlan
