/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-!
# Clearing open equations on a quasi-compact scheme

A section zero on an open is killed by a power of any global function whose
principal open lies there. The scheme need not be affine or reduced. A finite
family of sections shares a single exponent on the entire original scheme.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemeQuasiCompactOpenKernelPower
universe u
variable {U X : Scheme.{u}} [CompactSpace X] (f : U ⟶ X) [IsOpenImmersion f]

/-- Open vanishing on a quasi-compact scheme gives an actual global power annihilator. -/
theorem exists_pow_mul_eq_zero (a z : Γ(X, ⊤))
    (ha : X.basicOpen a ≤ f.opensRange) (hz : f.appTop z = 0) :
    ∃ k : ℕ, a ^ k * z = 0 := by
  let _ := f.isIso_app (X.basicOpen a) ha
  have he : algebraMap Γ(X, ⊤) Γ(X, X.basicOpen a) z = 0 := by
    apply (ConcreteCategory.bijective_of_isIso (f.app (X.basicOpen a))).injective
    rw [map_zero]
    exact (congrArg (fun g : Γ(X, ⊤) ⟶ Γ(U, f ⁻¹ᵁ X.basicOpen a) ↦ g z)
      (f.naturality (homOfLE (X.basicOpen_le a)).op)).trans (by
        change (U.presheaf.map _) (f.appTop z) = 0
        rw [hz, map_zero])
  exact exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact
    X isCompact_univ z a he

/-- A finite family has one global exponent, without separate exponents on affine charts. -/
theorem exists_pow_mul_eq_zero_finite {I : Type*} [Finite I]
    (a : Γ(X, ⊤)) (z : I → Γ(X, ⊤))
    (ha : X.basicOpen a ≤ f.opensRange) (hz : ∀ i, f.appTop (z i) = 0) :
    ∃ k : ℕ, ∀ i, a ^ k * z i = 0 := by
  classical
  let _ := Fintype.ofFinite I
  choose k hk using fun i ↦ exists_pow_mul_eq_zero f a (z i) ha (hz i)
  refine ⟨Finset.univ.sup k, fun i ↦ ?_⟩
  have hi : k i ≤ Finset.univ.sup k := Finset.le_sup (f := k) (Finset.mem_univ i)
  obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hi
  rw [hj, pow_add, mul_comm (a ^ k i), mul_assoc, hk i, mul_zero]

/-- Clearing a finite family of equalities retains both full sections and all nilpotents. -/
theorem exists_pow_mul_eq_finite {I : Type*} [Finite I]
    (a : Γ(X, ⊤)) (z w : I → Γ(X, ⊤))
    (ha : X.basicOpen a ≤ f.opensRange) (hz : ∀ i, f.appTop (z i) = f.appTop (w i)) :
    ∃ k : ℕ, ∀ i, a ^ k * z i = a ^ k * w i := by
  obtain ⟨k, hk⟩ := exists_pow_mul_eq_zero_finite f a (fun i ↦ z i - w i) ha
    (fun i ↦ by rw [map_sub, hz i, sub_self])
  exact ⟨k, fun i ↦ sub_eq_zero.mp (by simpa only [mul_sub] using hk i)⟩

end FLT.Mazur.SchemeQuasiCompactOpenKernelPower
