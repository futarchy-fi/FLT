/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.InvariantLocalizationNumerator

/-!
# Invariants commute with localization at a fixed function

The fixed ring in an equivariant principal localization is the principal
localization of the original fixed ring. The comparison retains the actual
inclusion of invariant numerators. The canonical action supplies an instance
of this result without requiring any localization action as input.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteGroupQuotient

variable (G A : Type*) [Group G] [CommRing A] [MulSemiringAction G A]

/-- An invariant element is a unit in the fixed ring if it is a unit in the ambient ring. -/
theorem invariant_isUnit (a : invariantRing G A) (ha : IsUnit (a : A)) : IsUnit a := by
  obtain ⟨u, hu⟩ := ha
  have hinv : ∀ g : G, g • (↑u⁻¹ : A) = ↑u⁻¹ := by
    intro g
    apply u.isUnit.mul_left_cancel
    calc
      (u : A) * (g • (↑u⁻¹ : A)) = g • ((u : A) * (↑u⁻¹ : A)) := by
        rw [smul_mul', hu, a.property g]
      _ = 1 := by rw [Units.mul_inv, smul_one]
      _ = (u : A) * (↑u⁻¹ : A) := (Units.mul_inv u).symm
  refine ⟨⟨a, ⟨↑u⁻¹, hinv⟩, ?_, ?_⟩, rfl⟩
  · apply Subtype.ext
    change (a : A) * (↑u⁻¹ : A) = 1
    rw [← hu, Units.mul_inv]
  · apply Subtype.ext
    change (↑u⁻¹ : A) * (a : A) = 1
    rw [← hu, Units.inv_mul]

variable (S : Type*) [CommRing S] [Algebra A S] [MulSemiringAction G S]
  (he : ∀ (g : G) a, g • algebraMap A S a = algebraMap A S (g • a))

/-- The original localization map restricted to the actual fixed subrings. -/
def invariantLocalizationMap : invariantRing G A →+* invariantRing G S :=
  lift G S ((algebraMap A S).comp (inclusion G A)) (by
    intro g a
    change g • algebraMap A S (a : A) = algebraMap A S (a : A)
    rw [he, a.property g])

variable [Finite G] (r : invariantRing G A) [IsLocalization.Away (r : A) S]

/-- The fixed subring satisfies the localization universal property at the fixed denominator. -/
theorem invariants_away :
    let _ := (invariantLocalizationMap G A S he).toAlgebra
    IsLocalization.Away r (invariantRing G S) := by
  let _ := (invariantLocalizationMap G A S he).toAlgebra
  apply IsLocalization.Away.mk
  · apply invariant_isUnit G S
    exact IsLocalization.Away.algebraMap_isUnit (r : A)
  · intro x
    obtain ⟨n, a, ha⟩ := exists_invariant_numerator G A r S he (x : S) x.property
    exact ⟨n, a, Subtype.ext ha⟩
  · intro a b hab
    have hab' : algebraMap A S (a : A) = algebraMap A S (b : A) :=
      congrArg Subtype.val hab
    obtain ⟨n, hn⟩ := IsLocalization.Away.exists_of_eq (r : A) hab'
    exact ⟨n, Subtype.ext hn⟩

/-- The actual principal-localization comparison is an algebra isomorphism. -/
def invariantLocalizationEquiv :
    let _ := (invariantLocalizationMap G A S he).toAlgebra
    Localization.Away r ≃ₐ[invariantRing G A] invariantRing G S := by
  let _ := (invariantLocalizationMap G A S he).toAlgebra
  let _ := invariants_away G A S he r
  exact IsLocalization.algEquiv (Submonoid.powers r) _ _

/-- Apply the comparison to the canonical localization action already constructed. -/
def canonicalInvariantLocalizationEquiv :
    let _ := localizedAction G A r
    Localization.Away r ≃+* invariantRing G (Localization.Away (r : A)) := by
  let _ := localizedAction G A r
  let _ := (invariantLocalizationMap G A (Localization.Away (r : A))
    (localizedAction_smul G A r)).toAlgebra
  exact (invariantLocalizationEquiv G A (Localization.Away (r : A))
    (localizedAction_smul G A r) r).toRingEquiv

end FLT.Mazur.FiniteGroupQuotient
