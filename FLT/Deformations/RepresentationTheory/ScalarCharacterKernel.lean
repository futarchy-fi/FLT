/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.RepresentationTheory.RankOneScalarCharacter
public import Mathlib.RepresentationTheory.Basic

/-!
# Extracting a scalar character with the original representation kernel

An action commuting with a rank-one scalar field determines a character.
The character detects exactly which group elements act trivially on the
original vector space; no faithfulness hypothesis is needed.
-/

@[expose] public noncomputable section
namespace Representation

variable {k F G V : Type*} [Field k] [Field F] [Group G]
  [AddCommGroup V] [Module k V] [Module F V]
  (ρ : Representation k G V)

/-- The scalar character has exactly the kernel of the original representation. -/
theorem scalar_character_ker_eq (hdim : Module.finrank F V = 1)
    (χ : G →* Fˣ) (hχ : ∀ g x, ρ g x = (χ g : F) • x) :
    χ.ker = ρ.toHomUnits.ker := by
  let e : F ≃ₗ[F] V := (Module.nonempty_linearEquiv_of_finrank_eq_one hdim).some
  ext g
  change χ g = 1 ↔ ρ.toHomUnits g = 1
  constructor
  · intro hg
    apply Units.ext
    apply LinearMap.ext
    intro x
    simpa [hg] using hχ g x
  · intro hg
    apply Units.ext
    have hx : ρ g (e 1) = e 1 := congrArg (fun u : (Module.End k V)ˣ ↦ u.val (e 1)) hg
    rw [hχ] at hx
    have he := congrArg e.symm hx
    simpa using he

/-- Extract a character and its action formula from the proved scalar-field action. -/
theorem exists_scalar_character_with_kernel (hdim : Module.finrank F V = 1)
    (hcomm : ∀ (a : F) g x, ρ g (a • x) = a • ρ g x) :
    ∃ χ : G →* Fˣ, (∀ g x, ρ g x = (χ g : F) • x) ∧ χ.ker = ρ.toHomUnits.ker := by
  let : DistribMulAction G V := {
    smul := fun g x ↦ ρ g x
    one_smul := fun x ↦ LinearMap.congr_fun ρ.map_one x
    mul_smul := fun g h x ↦ LinearMap.congr_fun (ρ.map_mul g h) x
    smul_zero := fun g ↦ (ρ g).map_zero
    smul_add := fun g x y ↦ (ρ g).map_add x y }
  let : SMulCommClass F G V := ⟨fun a g x ↦ (hcomm a g x).symm⟩
  obtain ⟨χ, hχ⟩ := exists_rank_one_scalar_character (G := G) hdim
  exact ⟨χ, hχ, ρ.scalar_character_ker_eq hdim χ hχ⟩

end Representation
