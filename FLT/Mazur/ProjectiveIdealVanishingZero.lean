/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProjectiveIdealVanishingScheme

/-!
# Zero coefficient ideals detect the entire original ideal

The vanishing equations are empty precisely when the map, or algebra ideal,
is already zero. This detects the actual ideal rather than its support.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.ProjectiveTargetVanishing
variable {R M N : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N]
  [Module R M] [Module R N] [Module.Projective R N] (f : M →ₗ[R] N)

/-- The projective coefficient ideal is zero exactly when the original map is zero. -/
theorem ideal_eq_bot_iff : ideal f = ⊥ ↔ f = 0 := by
  rw [ideal, FreeTargetVanishing.ideal_eq_bot_iff]
  constructor
  · intro h
    have he := congrArg (fun k : M →ₗ[R] N →₀ R ↦
      (Finsupp.linearCombination R id).comp k) h
    simpa only [← LinearMap.comp_assoc, retraction_embedding,
      LinearMap.id_comp, LinearMap.comp_zero] using he
  · rintro rfl
    exact LinearMap.comp_zero _

end FLT.Mazur.ProjectiveTargetVanishing

namespace FLT.Mazur.ProjectiveIdealVanishing
variable (R B : Type) [CommRing R] [CommRing B] [Algebra R B]
  [Module.Projective R B] (J : Ideal B)

/-- No coefficient equations remain exactly when the full original algebra ideal is zero. -/
theorem ideal_eq_bot_iff : ideal R B J = ⊥ ↔ J = ⊥ := by
  rw [ideal, ProjectiveTargetVanishing.ideal_eq_bot_iff]
  constructor
  · intro h
    apply le_bot_iff.mp
    intro x hx
    exact congrArg (fun f : J →ₗ[R] B ↦ f ⟨x, hx⟩) h
  · intro h
    ext x
    exact (show (x : B) = 0 from Ideal.mem_bot.mp (h ▸ x.property))

end FLT.Mazur.ProjectiveIdealVanishing
