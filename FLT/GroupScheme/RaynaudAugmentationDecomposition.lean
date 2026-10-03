/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudCharacterDecomposition
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Decomposing the augmentation ideal over the strict Henselian base

The scalar unit group has invertible order because the finite scalar field
and the residue field have the same characteristic. Thus the character
system and the augmentation decomposition need no additional splitting data.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan
open IsLocalRing

variable {R K F : Type} [CommRing R] [IsDomain R] [HenselianLocalRing R]
  [IsSepClosed (ResidueField R)] [Field K] [Algebra R K] [Field F] [Fintype F]

omit [IsDomain R] [IsSepClosed (ResidueField R)] in
/-- The scalar unit group has order minus one in the residue field. -/
theorem scalar_units_card_residue [DecidableEq F] (p : ℕ) [CharP F p] [CharP (ResidueField R) p] :
    (Fintype.card Fˣ : ResidueField R) = -1 := by
  have hc : (Fintype.card F : ResidueField R) = 0 := by
    rw [CharP.cast_eq_zero_iff (ResidueField R) p]
    exact (CharP.cast_eq_zero_iff F p _).mp (FiniteField.cast_card_eq_zero F)
  rw [Fintype.card_units, Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr Fintype.card_ne_zero),
    hc, Nat.cast_one, zero_sub]

omit [Fintype F] in
/-- The actual scalar action gives the full augmentation-character decomposition. -/
theorem FF.exists_augmentation_decomposition [Finite F] (X : FF R K)
    (p : ℕ) [CharP F p] [CharP (ResidueField R) p]
    (lift : F → ModelHom X X) (h1 : lift 1 = BialgHom.id R X.CoordinateRing)
    (hmul : ∀ a b, lift (a * b) = (lift b).comp (lift a)) :
    Nonempty (X.augmentation ≃ₗ[R] ((χ : Fˣ →* Rˣ) →
      CharacterProjector.eigenspace (X.augmentationRepresentation lift h1 hmul) χ)) := by
  classical
  let : Fintype F := Fintype.ofFinite _
  obtain ⟨hroots, hunit, _⟩ := henselian_group_characters (R := R) Fˣ (by
    rw [scalar_units_card_residue (F := F) p]; exact neg_ne_zero.mpr one_ne_zero)
  let : HasEnoughRootsOfUnity R (Monoid.exponent Fˣ) := hroots
  let : Invertible (Fintype.card Fˣ : R) := hunit.invertible
  let : Fintype (Fˣ →* Rˣ) := Fintype.ofFinite _
  exact ⟨CharacterProjector.decomposition (X.augmentationRepresentation lift h1 hmul)⟩

end ThreeAdicPlan
