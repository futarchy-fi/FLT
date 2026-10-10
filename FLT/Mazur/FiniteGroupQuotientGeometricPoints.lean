/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteGroupFieldPointOrbits
public import FLT.Mazur.IntegralAlgebraicallyClosedLifting

/-!
# Geometric points of affine finite-group quotients

For an algebraically closed field, maps from the actual invariant ring are in
bijection with group orbits of maps from the original coordinate ring. The
surjectivity proof lifts points across the integral inclusion; injectivity is
the polynomial orbit-separation theorem. Neither freeness nor tame characteristic
is assumed.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteGroupQuotient

variable (G A K : Type*) [Group G] [Finite G] [CommRing A] [MulSemiringAction G A]
  [Field K]

/-- The actual orbit relation on field-valued coordinate maps. -/
def fieldPointSetoid : Setoid (A →+* K) where
  r φ ψ := ∃ g : G, ψ = φ.comp (MulSemiringAction.toRingHom G A g)
  iseqv :=
    ⟨fun φ ↦ (ringHom_invariants_eq_iff G A φ φ).mp rfl,
      fun {φ ψ} h ↦ (ringHom_invariants_eq_iff G A ψ φ).mp
        ((ringHom_invariants_eq_iff G A φ ψ).mpr h).symm,
      fun {φ ψ χ} h₁ h₂ ↦ (ringHom_invariants_eq_iff G A φ χ).mp
        (((ringHom_invariants_eq_iff G A φ ψ).mpr h₁).trans
          ((ringHom_invariants_eq_iff G A ψ χ).mpr h₂))⟩

/-- Restriction to the invariant ring descends to the set of actual group orbits. -/
def fieldPointMap : Quotient (fieldPointSetoid G A K) → (invariantRing G A →+* K) :=
  Quotient.lift (fun φ ↦ φ.comp (inclusion G A))
    (fun φ ψ h ↦ (ringHom_invariants_eq_iff G A φ ψ).mpr h)

/-- Different field-valued orbits remain different on the invariant ring. -/
theorem fieldPointMap_injective : Function.Injective (fieldPointMap G A K) := by
  intro x y
  refine Quotient.inductionOn₂ x y fun φ ψ h ↦ ?_
  exact Quotient.sound ((ringHom_invariants_eq_iff G A φ ψ).mp h)

/-- Every algebraically closed point of the invariant ring lifts to the original ring. -/
theorem fieldPointMap_surjective [IsAlgClosed K] : Function.Surjective (fieldPointMap G A K) := by
  let _ := Algebra.IsInvariant.isIntegral (invariantRing G A) A G
  intro f
  obtain ⟨g, hg⟩ := exists_ringHom_of_integral (invariantRing G A) A f
  exact ⟨Quotient.mk _ g, hg⟩

/-- The affine quotient has exactly the geometric point orbits, including stabilizers. -/
theorem fieldPointMap_bijective [IsAlgClosed K] : Function.Bijective (fieldPointMap G A K) :=
  ⟨fieldPointMap_injective G A K, fieldPointMap_surjective G A K⟩

/-- The geometric-point classification as an explicit equivalence of types. -/
def fieldPointEquiv [IsAlgClosed K] :
    Quotient (fieldPointSetoid G A K) ≃ (invariantRing G A →+* K) :=
  Equiv.ofBijective (fieldPointMap G A K) (fieldPointMap_bijective G A K)

end FLT.Mazur.FiniteGroupQuotient
