/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudRootReduction
public import FLT.GroupScheme.RaynaudAugmentationDecomposition

/-!
# Fundamental characters over the strict Henselian base

Embed the finite scalar field into the separably closed residue field, then
lift its unit character along the roots-of-unity reduction isomorphism.
Its powers give the Frobenius cycle used in the cyclic equations.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan
open IsLocalRing

variable {R F : Type} [CommRing R] [IsDomain R] [HenselianLocalRing R]
  [IsSepClosed (ResidueField R)] [Field F] [Fintype F] [DecidableEq F]
  (p : ℕ) [CharP F p] [CharP (ResidueField R) p]

include p in
omit [IsDomain R] [Fintype F] [DecidableEq F] in
/-- The finite scalar field embeds into the actual separably closed residue field. -/
theorem exists_scalar_residue_embedding [Finite F] : Nonempty (F →+* ResidueField R) := by
  let : Fintype F := Fintype.ofFinite _
  have : Fact p.Prime := ⟨CharP.char_is_prime F p⟩
  let : Algebra (ZMod p) F := (ZMod.castHom (dvd_refl p) F).toAlgebra
  let : Algebra (ZMod p) (ResidueField R) :=
    (ZMod.castHom (dvd_refl p) (ResidueField R)).toAlgebra
  exact ⟨(IsSepClosed.lift (K := ZMod p) (L := F) (M := ResidueField R)).toRingHom⟩

/-- Lift the unit character of a chosen residue-field embedding multiplicatively. -/
def fundamentalCharacter (e : F →+* ResidueField R) : Fˣ →* Rˣ := by
  let n := Fintype.card Fˣ
  have hn : (n : ResidueField R) ≠ 0 := by
    rw [scalar_units_card_residue (F := F) p]; exact neg_ne_zero.mpr one_ne_zero
  let f : Fˣ →* rootsOfUnity n (ResidueField R) :=
    { toFun := fun a ↦ ⟨Units.map e.toMonoidHom a, by
        rw [mem_rootsOfUnity, ← map_pow, pow_card_eq_one, map_one]⟩
      map_one' := by ext; simp
      map_mul' a b := by ext; simp }
  exact (rootsOfUnity n R).subtype.comp ((rootReductionEquiv hn).symm.toMonoidHom.comp f)

/-- Reduction of the lifted character is the prescribed field embedding. -/
theorem fundamentalCharacter_residue (e : F →+* ResidueField R) (a : Fˣ) :
    residue R (fundamentalCharacter p e a : R) = e a := by
  have hn : (Fintype.card Fˣ : ResidueField R) ≠ 0 := by
    rw [scalar_units_card_residue (F := F) p]; exact neg_ne_zero.mpr one_ne_zero
  let y : rootsOfUnity (Fintype.card Fˣ) (ResidueField R) :=
    ⟨Units.map e.toMonoidHom a, by
      rw [mem_rootsOfUnity, ← map_pow, pow_card_eq_one, map_one]⟩
  have h := (rootReductionEquiv hn).apply_symm_apply y
  exact congrArg (fun z : rootsOfUnity (Fintype.card Fˣ) (ResidueField R) ↦
    (z.val : ResidueField R)) h

/-- The lifted fundamental character is faithful on scalar units. -/
theorem fundamentalCharacter_injective (e : F →+* ResidueField R) :
    Function.Injective (fundamentalCharacter p e) := by
  intro a b h
  apply Units.ext
  apply e.injective
  have h' := congrArg (fun z : Rˣ ↦ residue R (z : R)) h
  simpa only [fundamentalCharacter_residue] using h'

/-- Frobenius powers of the lift reduce to the corresponding field embeddings. -/
theorem fundamentalCharacter_pow_residue (e : F →+* ResidueField R) (i : ℕ) (a : Fˣ) :
    residue R (((fundamentalCharacter p e ^ (p ^ i)) a : Rˣ) : R) = e a ^ (p ^ i) := by
  simp [fundamentalCharacter_residue]

/-- The finite scalar field makes the character Frobenius powers periodic. -/
theorem fundamentalCharacter_periodic (e : F →+* ResidueField R) (r : ℕ)
    (hr : Fintype.card F = p ^ r) :
    fundamentalCharacter p e ^ (p ^ r) = fundamentalCharacter p e := by
  apply MonoidHom.ext
  intro a
  change (fundamentalCharacter p e a) ^ (p ^ r) = _
  rw [← map_pow, ← hr]
  congr 1
  apply Units.ext
  exact FiniteField.pow_card (a : F)

end ThreeAdicPlan
