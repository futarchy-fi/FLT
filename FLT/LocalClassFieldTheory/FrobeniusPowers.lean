/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.Frobenius

/-!
# Powers of arithmetic Frobenius on residue classes

Iteration of the residue power rule identifies every nonnegative power of
Frobenius, including the residue-degree power needed for change of base.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open IsLocalRing

variable (R S K L : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
  [Algebra S L] [IsFractionRing S L] [Algebra R S] [Algebra K L] [Algebra R L]
  [IsScalarTower R K L] [IsScalarTower R S L] [IsIntegralClosure S R L]
  [FiniteDimensional K L] [IsGalois K L] [IsLocalHom (algebraMap R S)]
  [Algebra.FormallyUnramified R S] [Finite (ResidueField R)]

/-- The nth power of Frobenius raises residues to the q^n power. -/
theorem arithmeticFrobenius_pow_residue (n : ℕ) (x : ResidueField S) :
    residueGaloisAction R S K L (arithmeticFrobenius R S K L ^ n) x =
      x ^ (Nat.card (ResidueField R) ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', map_mul, AlgEquiv.mul_apply, ih,
      arithmeticFrobenius_residue, ← pow_mul, Nat.pow_succ]

/-- The q^n residue rule uniquely characterizes the nth Frobenius power. -/
theorem arithmeticFrobenius_pow_unique (n : ℕ) (σ : Gal(L/K))
    (hσ : ∀ x : S, residue S (galRestrict R K L S σ x) =
      residue S x ^ (Nat.card (ResidueField R) ^ n)) :
    σ = arithmeticFrobenius R S K L ^ n := by
  apply residueGaloisAction_injective R S K L
  ext x
  obtain ⟨x, rfl⟩ := residue_surjective x
  exact (hσ x).trans (arithmeticFrobenius_pow_residue R S K L n (residue S x)).symm

end LocalClassFieldTheory
