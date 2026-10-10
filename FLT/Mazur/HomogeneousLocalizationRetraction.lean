/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HomogeneousFractionProjection

/-!
# A linear retraction onto homogeneous localization

Projecting each numerator to the degree of its denominator splits the inclusion
of degree-zero fractions into ordinary localization. This is linear over the
structural coefficient ring and needs no flatness hypothesis.
-/

@[expose] public noncomputable section

open HomogeneousLocalization
open scoped FLT.Mazur.HomogeneousLocalizationScalars

universe u

namespace FLT.Mazur.HomogeneousLocalizationRetraction

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open HomogeneousFractionProjection

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] {f : A} {d : ℕ} (hf : f ∈ 𝒜 d)

/-- Every ordinary localized element has a numerator and a power denominator. -/
theorem presentation (x : Localization.Away f) : ∃ k : ℕ, ∃ a : A,
    (Localization.mk a ⟨f ^ k, ⟨k, rfl⟩⟩ : Localization.Away f) = x := by
  induction x using Localization.induction_on with
  | H x =>
    rcases x with ⟨a, _, k, rfl⟩
    exact ⟨k, a, rfl⟩

/-- Project an ordinary localized element to its degree-zero fraction. -/
def projection (x : Localization.Away f) : Away 𝒜 f :=
  fraction 𝒜 hf (presentation x).choose (presentation x).choose_spec.choose

/-- Projection has the prescribed value on every power-denominator presentation. -/
theorem projection_mk (k : ℕ) (a : A) :
    projection 𝒜 hf (Localization.mk a ⟨f ^ k, ⟨k, rfl⟩⟩) =
      fraction 𝒜 hf k a :=
  fraction_eq 𝒜 hf _ _ _ _ (presentation _).choose_spec.choose_spec

/-- Projected fractions add with their original common denominator. -/
theorem fraction_add (k l : ℕ) (a b : A) :
    fraction 𝒜 hf (k + l) (f ^ k * b + f ^ l * a) =
      fraction 𝒜 hf k a + fraction 𝒜 hf l b := by
  apply HomogeneousLocalization.val_injective
  simp only [fraction, Away.val_mk, val_add, Localization.add_mk, map_add]
  rw [project_pow_mul 𝒜 hf l k,
    show k + l = l + k by omega, project_pow_mul 𝒜 hf k l]
  congr 1
  apply Subtype.ext
  exact (pow_add f l k).trans (mul_comm _ _)

/-- Projection preserves addition of arbitrary ordinary fractions. -/
theorem projection_add (x y : Localization.Away f) :
    projection 𝒜 hf (x + y) = projection 𝒜 hf x + projection 𝒜 hf y := by
  obtain ⟨k, a, rfl⟩ := presentation x
  obtain ⟨l, b, rfl⟩ := presentation y
  rw [Localization.add_mk]
  have he : (⟨f ^ k, ⟨k, rfl⟩⟩ : Submonoid.powers f) *
      ⟨f ^ l, ⟨l, rfl⟩⟩ =
        ⟨f ^ (k + l), ⟨(k + l), rfl⟩⟩ :=
    Subtype.ext (pow_add f k l).symm
  rw [he, projection_mk, projection_mk, projection_mk]
  exact fraction_add 𝒜 hf k l a b

/-- Projection is linear for the original structural scalars. -/
theorem projection_smul (r : R) (x : Localization.Away f) :
    projection 𝒜 hf (r • x) = r • projection 𝒜 hf x := by
  obtain ⟨k, a, rfl⟩ := presentation x
  rw [Localization.smul_mk, projection_mk, projection_mk]
  apply HomogeneousLocalization.val_injective
  simp only [fraction, Away.val_mk, val_smul, map_smul, Localization.smul_mk]

/-- The homogeneous fraction projection as a linear map over the original coefficients. -/
def linearProjection : Localization.Away f →ₗ[R] Away 𝒜 f where
  toFun := projection 𝒜 hf
  map_add' := projection_add 𝒜 hf
  map_smul' := projection_smul 𝒜 hf

/-- The constructed projection fixes every actual degree-zero fraction. -/
theorem linearProjection_val (x : Away 𝒜 f) : linearProjection 𝒜 hf x.val = x := by
  obtain ⟨k, a, ha, rfl⟩ := Away.mk_surjective 𝒜 hf x
  change projection 𝒜 hf (Away.mk 𝒜 hf k a ha).val = _
  rw [Away.val_mk, projection_mk]
  apply HomogeneousLocalization.val_injective
  simp only [fraction, Away.val_mk]
  congr 1
  change (DirectSum.decompose 𝒜 a (k * d) : A) = a
  exact DirectSum.decompose_of_mem_same 𝒜 (by simpa only [nsmul_eq_mul, Nat.cast_id] using ha)

end FLT.Mazur.HomogeneousLocalizationRetraction
