/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudActualCyclicPresentation
public import FLT.GroupScheme.RaynaudCoefficientBounds

/-!
# Complementary products for the derived cyclic coefficients

Frobenius periodicity identifies the next character in the finite cycle.
The universal fundamental calculation then applies to the exact coefficients
chosen for the actual polynomial presentation.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan
open IsLocalRing

section Characters
variable {R F : Type} [CommRing R] [IsDomain R] [HenselianLocalRing R]
  [IsSepClosed (ResidueField R)] [Field F] [Fintype F] [DecidableEq F]
  (p : ℕ) [CharP F p] [CharP (ResidueField R) p] (e : F →+* ResidueField R)
  (r : ℕ+) (hr : Fintype.card F = p ^ (r : ℕ))

include hr in
/-- Raising a fundamental cycle character to p gives its cyclic successor. -/
theorem fundamentalCharacter_cycle_pow (i : Fin r) :
    (fundamentalCharacter p e ^ (p ^ i.val)) ^ p =
      fundamentalCharacter p e ^ (p ^ (cycleNext r i).val) := by
  have hper : Function.Periodic (fun j ↦ fundamentalCharacter p e ^ (p ^ j)) (r : ℕ) := by
    intro j
    dsimp only
    rw [pow_add, mul_comm (p ^ j), pow_mul, fundamentalCharacter_periodic p e r hr]
  rw [← pow_mul, ← pow_succ]
  exact (hper.map_mod_nat (i.val + 1)).symm
end Characters

variable {R K F : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [HenselianLocalRing R] [IsSepClosed (ResidueField R)] [Field K] [Algebra R K]
  [CharZero K] [IsFractionRing R K] [Field F] [Fintype F] [DecidableEq F]
  [Invertible (Fintype.card Fˣ : R)] (X : FF R K) [Module F X.Points]
  (lift : F → ModelHom X X) (h0 : lift 0 = ModelHom.zero X X)
  (h1 : lift 1 = BialgHom.id R X.CoordinateRing)
  (hmul : ∀ a b, lift (a * b) = (lift b).comp (lift a))
  (hadd : ∀ a b, lift (a + b) = (lift a).add (lift b))
  (p : ℕ) [CharP F p] [CharP (ResidueField R) p]
  (hdim : Module.finrank F X.Points = 1)
  (hlift : ∀ a x, genericHom (lift a) x = a • x) (e : F →+* ResidueField R)
  (r : ℕ+) (hr : Fintype.card F = p ^ (r : ℕ))

include h0 hadd in
/-- Each chosen cyclic coefficient has an actual complementary p-times-unit product. -/
theorem FF.fundamentalCoefficient_complement (i : Fin r) :
    ∃ (b : R) (u : Rˣ),
      X.fundamentalCoefficient lift h1 hmul p hdim hlift e r hr i * b = (p : R) * u := by
  let : Fact p.Prime := ⟨CharP.char_is_prime F p⟩
  apply X.exists_complementary_prime_coefficient lift h0 h1 hmul hadd p hdim hlift
    (fundamentalCharacter p e ^ (p ^ i.val))
    ((iterateFrobenius (ResidueField R) p i.val).comp e)
    (fundamentalCharacter_pow_residue p e i.val)
  rw [fundamentalCharacter_cycle_pow p e r hr i]
  exact X.fundamentalCoefficient_spec lift h1 hmul p hdim hlift e r hr i

end ThreeAdicPlan
