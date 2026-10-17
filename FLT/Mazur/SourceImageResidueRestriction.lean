/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SourceImageNakayama

/-!
# Residue restriction tests in the source

Reducing the source, rather than the ambient target of a connecting map,
retains the entire relative obstruction. For a finite connecting image over
a local ring, surjectivity of this residue restriction gives exact lifts.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.SourceImageNakayama
variable {R U D M : Type*} [CommRing R]
  [AddCommGroup U] [Module R U] [AddCommGroup D] [Module R D]
  [AddCommGroup M] [Module R M]

/-- The original restriction followed by reduction of its target module. -/
def residueRestriction (ρ : U →ₗ[R] D) (J : Ideal R) :
    U →ₗ[R] D ⧸ J • (⊤ : Submodule R D) :=
  (J • (⊤ : Submodule R D)).mkQ.comp ρ

/-- Residue restriction is onto exactly when restrictions span the source modulo the ideal. -/
theorem residueRestriction_surjective_iff (ρ : U →ₗ[R] D) (J : Ideal R) :
    Function.Surjective (residueRestriction ρ J) ↔
      LinearMap.range ρ ⊔ J • (⊤ : Submodule R D) = ⊤ := by
  rw [← LinearMap.range_eq_top, residueRestriction, LinearMap.range_comp,
    Submodule.map_mkQ_eq_top, sup_comm]

/-- A source residue lift is an approximate original lift with error in the source ideal. -/
theorem residueRestriction_surjective_iff_lifts (ρ : U →ₗ[R] D) (J : Ideal R) :
    Function.Surjective (residueRestriction ρ J) ↔
      ∀ t : D, ∃ v : U, t - ρ v ∈ J • (⊤ : Submodule R D) := by
  constructor
  · intro h t
    obtain ⟨v, hv⟩ := h ((J • (⊤ : Submodule R D)).mkQ t)
    refine ⟨v, ?_⟩
    apply (Submodule.Quotient.mk_eq_zero _).mp
    change (J • (⊤ : Submodule R D)).mkQ (t - ρ v) = 0
    rw [map_sub, ← hv]
    exact sub_self _
  · intro h x
    obtain ⟨t, rfl⟩ := (J • (⊤ : Submodule R D)).mkQ_surjective x
    obtain ⟨v, hv⟩ := h t
    refine ⟨v, ?_⟩
    change (J • (⊤ : Submodule R D)).mkQ (ρ v) =
      (J • (⊤ : Submodule R D)).mkQ t
    have hz := (Submodule.Quotient.mk_eq_zero _).mpr hv
    change (J • (⊤ : Submodule R D)).mkQ (t - ρ v) = 0 at hz
    rw [map_sub, sub_eq_zero] at hz
    exact hz.symm

variable [IsLocalRing R] (ρ : U →ₗ[R] D) (g : D →ₗ[R] M)
  (hker : LinearMap.ker g = LinearMap.range ρ)

include hker in
/-- For a finite relative image, source residue lifts construct exact restriction lifts. -/
theorem surjective_of_residueRestriction (hfg : (LinearMap.range g).FG)
    (hres : Function.Surjective (residueRestriction ρ (IsLocalRing.maximalIdeal R))) :
    Function.Surjective ρ := by
  have hz := eq_zero_of_residue ρ g hker hfg (IsLocalRing.maximalIdeal R)
    (IsLocalRing.maximalIdeal_le_jacobson ⊥)
    ((residueRestriction_surjective_iff ρ _).mp hres)
  rw [← LinearMap.range_eq_top, ← hker, hz, LinearMap.ker_zero]

end FLT.Mazur.SourceImageNakayama
