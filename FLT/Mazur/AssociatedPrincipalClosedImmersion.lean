/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AssociatedPrimePowerDetection
public import FLT.Mazur.SchemeQuasiCompactOpenKernelPower
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Closed immersions detected on associated principal neighborhoods

Local sections on principal neighborhoods of the associated coefficient
primes kill the entire closed-immersion ideal, including embedded nilpotents.
For an affine target this constructs an isomorphism. The neighborhoods need
not cover every point.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.AssociatedPrincipalClosedImmersion
variable {Z X : Scheme.{0}} [CompactSpace X] [IsNoetherianRing Γ(X, ⊤)]

/-- Principal local sections at associated primes kill the whole global equation ideal. -/
theorem kernel_eq_bot (f : Z ⟶ X)
    (h : ∀ P ∈ associatedPrimes Γ(X, ⊤) Γ(X, ⊤),
      ∃ a : Γ(X, ⊤), a ∉ P ∧
        ∃ d : (X.basicOpen a).toScheme ⟶ Z, d ≫ f = (X.basicOpen a).ι) :
    RingHom.ker f.appTop.hom = ⊥ := by
  apply le_antisymm _ bot_le
  intro r hr
  change r = 0
  apply AssociatedPrimePowerDetection.eq_zero_of_associated_powers (R := Γ(X, ⊤))
  intro P hP
  obtain ⟨a, ha, d, hd⟩ := h P hP
  have hz : (X.basicOpen a).ι.appTop r = 0 := by
    rw [← hd, Scheme.Hom.comp_appTop]
    change d.appTop (f.appTop r) = 0
    rw [show f.appTop r = 0 from hr, map_zero]
  obtain ⟨k, hk⟩ := SchemeQuasiCompactOpenKernelPower.exists_pow_mul_eq_zero
    (X.basicOpen a).ι a r (by simp only [Scheme.Opens.opensRange_ι, le_refl]) hz
  exact ⟨a, ha, k, hk⟩

/-- An affine closed immersion with these associated local sections is an isomorphism. -/
theorem isIso_of_associated_sections [IsAffine X] (f : Z ⟶ X) [IsClosedImmersion f]
    (h : ∀ P ∈ associatedPrimes Γ(X, ⊤) Γ(X, ⊤),
      ∃ a : Γ(X, ⊤), a ∉ P ∧
        ∃ d : (X.basicOpen a).toScheme ⟶ Z, d ≫ f = (X.basicOpen a).ι) :
    IsIso f := by
  apply IsClosedImmersion.isIso_of_injective_of_isAffine
  exact (RingHom.injective_iff_ker_eq_bot _).mpr (kernel_eq_bot f h)

end FLT.Mazur.AssociatedPrincipalClosedImmersion
