/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudIntegralCharacterRank
public import FLT.GroupScheme.RaynaudAugmentationRank

/-!
# Derived rank-one integral eigenspaces

The augmentation rank equals the number of characters. Each character
summand has rank at most one, so every summand has rank exactly one.
Generators are then chosen from these proved rank-one modules.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan
open IsLocalRing

variable {R K F : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [HenselianLocalRing R] [IsSepClosed (ResidueField R)] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] [Field F] [Finite F]
  (X : FF R K) [Module F X.Points]
  (p : ℕ) [CharP F p] [CharP (ResidueField R) p]
  (lift : F → ModelHom X X) (h1 : lift 1 = BialgHom.id R X.CoordinateRing)
  (hmul : ∀ a b, lift (a * b) = (lift b).comp (lift a))

include p

/-- Every integral character summand has rank one, derived from the generic order. -/
theorem FF.integralCharacter_finrank (hdim : Module.finrank F X.Points = 1)
    (hlift : ∀ a x, genericHom (lift a) x = a • x) (χ : Fˣ →* Rˣ) :
    Module.finrank R (X.integralCharacter lift h1 hmul χ) = 1 := by
  classical
  let : Fintype F := Fintype.ofFinite _
  let : Fintype (Fˣ →* Rˣ) := Fintype.ofFinite _
  let : Module.Free R X.CoordinateRing := Module.free_of_flat_of_isLocalRing
  obtain ⟨hroots, _, he⟩ := henselian_group_characters (R := R) Fˣ (by
    rw [scalar_units_card_residue (F := F) p]; exact neg_ne_zero.mpr one_ne_zero)
  have hc : Fintype.card (Fˣ →* Rˣ) = Fintype.card F - 1 := by
    rw [Fintype.card_congr he.some.toEquiv, Fintype.card_units]
  have hpoints : Nat.card X.Points = Fintype.card F := by
    rw [← Nat.card_congr (Module.nonempty_linearEquiv_of_finrank_eq_one hdim).some.toEquiv]
    exact Nat.card_eq_fintype_card
  obtain ⟨e⟩ := X.exists_augmentation_decomposition p lift h1 hmul
  have hs := e.finrank_eq
  rw [Module.finrank_pi_fintype] at hs
  have ht := X.augmentation_finrank
  rw [hpoints, hs] at ht
  change 1 + (∑ ψ : Fˣ →* Rˣ,
    Module.finrank R (X.integralCharacter lift h1 hmul ψ)) = Fintype.card F at ht
  have hle (ψ : Fˣ →* Rˣ) :
      Module.finrank R (X.integralCharacter lift h1 hmul ψ) ≤ 1 :=
    Module.finrank_le_of_rank_le (X.integralCharacter_rank_le_one lift h1 hmul hdim hlift ψ)
  have heq : ∑ ψ : Fˣ →* Rˣ, Module.finrank R (X.integralCharacter lift h1 hmul ψ) =
      ∑ _ : Fˣ →* Rˣ, (1 : ℕ) := by
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one, hc]
    omega
  exact (Finset.sum_eq_sum_iff_of_le (fun ψ _ ↦ hle ψ)).mp heq χ (Finset.mem_univ χ)

/-- A generator is chosen only after proving the actual eigenspace has rank one. -/
theorem FF.exists_integralCharacter_basis (hdim : Module.finrank F X.Points = 1)
    (hlift : ∀ a x, genericHom (lift a) x = a • x) (χ : Fˣ →* Rˣ) :
    Nonempty (Module.Basis Unit R (X.integralCharacter lift h1 hmul χ)) := by
  let : Module.Free R X.CoordinateRing := Module.free_of_flat_of_isLocalRing
  exact (finrank_eq_one_iff Unit).mp
    (X.integralCharacter_finrank p lift h1 hmul hdim hlift χ)

end ThreeAdicPlan
