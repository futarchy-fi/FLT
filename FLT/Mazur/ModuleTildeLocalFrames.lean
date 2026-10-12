/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafLocalFrames

/-!
# Prescribed principal bases give prescribed sheaf frames

Keep the module and index type explicit while passing from an actual localized
basis to a frame. No freeness or rank conclusion is supplied as an extra field.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.ModuleTildeLocalFrames
universe u
variable {A : CommRingCat.{u}} (Q : ModuleCat.{u} A) (τ : Type u)

/-- Principal-local bases give fixed-type frames on actual open neighborhoods. -/
theorem hasFrames_of_principalBases
    (h : ∀ x : PrimeSpectrum A, ∃ r ∉ x.asIdeal,
      Nonempty (Module.Basis τ (Localization.Away r) (LocalizedModule.Away r Q))) :
    ModuleSheafLocalFrames.HasFrames τ (tilde Q) := by
  intro x
  obtain ⟨r, hr, ⟨b⟩⟩ := h x
  exact ⟨PrimeSpectrum.basicOpen r, hr,
    ⟨TildeFiniteFreeLocalization.basicOpenTrivialization Q r b⟩⟩

end FLT.Mazur.ModuleTildeLocalFrames
