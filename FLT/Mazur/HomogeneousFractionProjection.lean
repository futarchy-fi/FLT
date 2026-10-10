/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HomogeneousLocalizationScalars

/-!
# Projecting an ordinary fraction to its degree-zero part

For a homogeneous denominator, projecting the numerator to the denominator's
degree is independent of the chosen fraction presentation. This is the algebraic
step needed to split the inclusion of homogeneous into ordinary localization.
-/

@[expose] public noncomputable section

open HomogeneousLocalization

namespace FLT.Mazur.HomogeneousFractionProjection

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] {f : A} {d : ℕ} (hf : f ∈ 𝒜 d)

include hf in
/-- Projection commutes with a homogeneous power, shifting the projected degree. -/
theorem project_pow_mul (k l : ℕ) (a : A) :
    GradedAlgebra.proj 𝒜 ((l + k) * d) (f ^ l * a) =
      f ^ l * GradedAlgebra.proj 𝒜 (k * d) a := by
  rw [Nat.add_mul]
  exact DirectSum.coe_decompose_mul_add_of_left_mem 𝒜
    (show f ^ l ∈ 𝒜 (l * d) from by
      simpa only [nsmul_eq_mul, Nat.cast_id] using SetLike.pow_mem_graded l hf)

/-- The degree-zero fraction obtained by projecting its numerator. -/
def fraction (k : ℕ) (a : A) : Away 𝒜 f :=
  Away.mk 𝒜 hf k (GradedAlgebra.proj 𝒜 (k * d) a)
    (by
      change (DirectSum.decompose 𝒜 a (k * d) : A) ∈ 𝒜 (k * d)
      exact (DirectSum.decompose 𝒜 a (k * d)).property)

/-- Equal ordinary fractions have equal degree-zero projections. -/
theorem fraction_eq (k l : ℕ) (a b : A)
    (he : (Localization.mk a ⟨f ^ k, ⟨k, rfl⟩⟩ : Localization.Away f) =
      (Localization.mk b ⟨f ^ l, ⟨l, rfl⟩⟩ : Localization.Away f)) :
    fraction 𝒜 hf k a = fraction 𝒜 hf l b := by
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists] at he
  obtain ⟨⟨_, t, rfl⟩, ht⟩ := he
  apply HomogeneousLocalization.val_injective
  change Localization.mk _ ⟨f ^ k, _⟩ = Localization.mk _ ⟨f ^ l, _⟩
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨⟨f ^ t, ⟨t, rfl⟩⟩, ?_⟩
  have hp := congrArg (GradedAlgebra.proj 𝒜 ((t + l + k) * d)) ht
  change GradedAlgebra.proj 𝒜 ((t + l + k) * d) (f ^ t * (f ^ l * a)) =
    GradedAlgebra.proj 𝒜 ((t + l + k) * d) (f ^ t * (f ^ k * b)) at hp
  rw [← mul_assoc, ← pow_add, project_pow_mul 𝒜 hf k (t + l),
    show t + l + k = t + k + l from by omega,
    ← mul_assoc, ← pow_add, project_pow_mul 𝒜 hf l (t + k)] at hp
  simpa only [pow_add, mul_assoc] using hp

end FLT.Mazur.HomogeneousFractionProjection
