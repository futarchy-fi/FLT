/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudCharacterConstantBaseChange
public import FLT.GroupScheme.RaynaudCharacterFactorial
public import FLT.GroupScheme.RaynaudFundamentalCharacter
public import Mathlib.Data.Nat.Factorial.NatCast

/-!
# Single fundamental digit constants are units

The constructed fundamental character reduces to a field embedding.
Its n-fold constant therefore reduces to n!, which is nonzero for n < p.
No unit hypothesis is imposed on the model or on its power parameters.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan
open IsLocalRing CharacterAverage

variable {R F : Type} [CommRing R] [IsDomain R] [HenselianLocalRing R]
  [IsSepClosed (ResidueField R)] [Field F] [Fintype F] [DecidableEq F]
  [Invertible (Fintype.card Fˣ : R)]
  (p : ℕ) [CharP F p] [CharP (ResidueField R) p]
  (e : F →+* ResidueField R)

/-- The single-character constant has residue n factorial. -/
theorem fundamental_constant_residue (n : ℕ) (hn : n ≠ 0) :
    residue R (constant (fundamentalCharacter p e) (fundamentalCharacter p e ^ n) n) =
      (n.factorial : ResidueField R) := by
  let : Invertible (Fintype.card Fˣ : ResidueField R) :=
    (Invertible.map (residue R) (Fintype.card Fˣ : R)).copy _ (map_natCast _ _).symm
  rw [map_constant]
  have hp : mapCharacter (residue R) (fundamentalCharacter p e ^ n) =
      mapCharacter (residue R) (fundamentalCharacter p e) ^ n := by
    ext u
    simp [mapCharacter]
  rw [hp]
  apply constant_embedding_factorial _ e _ n hn
  intro u
  exact fundamentalCharacter_residue p e u

/-- Fewer than p repetitions of a fundamental character give a unit constant. -/
theorem isUnit_fundamental_digit_constant (n : ℕ) (hn : n ≠ 0) (hnp : n < p) :
    IsUnit (constant (fundamentalCharacter p e) (fundamentalCharacter p e ^ n) n) := by
  apply (residue_ne_zero_iff_isUnit _).mp
  rw [fundamental_constant_residue p e n hn]
  let : Fact p.Prime := ⟨CharP.char_is_prime F p⟩
  exact ((IsUnit.natCast_factorial_iff_of_charP p).mpr hnp).ne_zero

end ThreeAdicPlan
