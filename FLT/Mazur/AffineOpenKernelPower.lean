/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Powers annihilating functions invisible on an affine principal open

A function vanishing on an open subscheme is killed by a power of every
coordinate whose principal open lies inside that subscheme. The function
itself is retained, so this statement applies to nonreduced ideals.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.AffineOpenKernelPower
universe u
variable {U X : Scheme.{u}} [IsAffine X] (f : U ⟶ X) [IsOpenImmersion f]

/-- A function zero on an open subscheme is killed by a power of a coordinate it contains. -/
theorem exists_pow_mul_eq_zero (a z : Γ(X, ⊤))
    (ha : X.basicOpen a ≤ f.opensRange) (hz : f.appTop z = 0) :
    ∃ k : ℕ, a ^ k * z = 0 := by
  let _ := f.isIso_app (X.basicOpen a) ha
  have he : algebraMap Γ(X, ⊤) Γ(X, X.basicOpen a) z = 0 := by
    apply (ConcreteCategory.bijective_of_isIso (f.app (X.basicOpen a))).injective
    rw [map_zero]
    exact (congrArg (fun g : Γ(X, ⊤) ⟶ Γ(U, f ⁻¹ᵁ X.basicOpen a) ↦ g z)
      (f.naturality (homOfLE (X.basicOpen_le a)).op)).trans (by
        change (U.presheaf.map _ ) (f.appTop z) = 0
        rw [hz, map_zero])
  obtain ⟨⟨_, k, rfl⟩, hk⟩ :=
    (IsLocalization.map_eq_zero_iff (Submonoid.powers a) Γ(X, X.basicOpen a) z).mp he
  exact ⟨k, hk⟩

end FLT.Mazur.AffineOpenKernelPower
