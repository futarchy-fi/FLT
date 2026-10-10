/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Invariant.Basic

/-!
# Coordinate rings for finite group quotients

The fixed ring is the actual subring of invariant functions. An invariant map
from a test ring factors uniquely through its inclusion. No freeness or
invertibility of the group order is required.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteGroupQuotient

variable (G A : Type*) [Group G] [CommRing A] [MulSemiringAction G A]

/-- The coordinate ring of the affine quotient. -/
abbrev invariantRing := FixedPoints.subring A G

/-- The coordinate inclusion defining the quotient morphism. -/
def inclusion : invariantRing G A →+* A := (FixedPoints.subring A G).subtype

/-- The invariant coordinate inclusion is injective. -/
theorem inclusion_injective : Function.Injective (inclusion G A) := Subtype.val_injective

/-- Every element of the fixed ring is fixed by the given action. -/
theorem smul_inclusion (g : G) (a : invariantRing G A) :
    g • inclusion G A a = inclusion G A a := a.property g

/-- The inclusion realizes the invariant-extension predicate, without an extra hypothesis. -/
instance invariantExtension : Algebra.IsInvariant (invariantRing G A) A G where
  isInvariant a ha := ⟨⟨a, ha⟩, rfl⟩

variable {R : Type*} [CommRing R]

/-- An invariant map of coordinate rings factors through the actual fixed subring. -/
def lift (f : R →+* A) (hf : ∀ (g : G) r, g • f r = f r) : R →+* invariantRing G A :=
  f.codRestrict (FixedPoints.subring A G) (fun r g ↦ hf g r)

/-- Composing the factorization with the inclusion recovers the original map. -/
@[simp]
theorem inclusion_comp_lift (f : R →+* A) (hf : ∀ (g : G) r, g • f r = f r) :
    (inclusion G A).comp (lift G A f hf) = f := rfl

/-- The inclusion detects equality of coordinate maps. -/
theorem inclusion_comp_injective :
    Function.Injective (fun f : R →+* invariantRing G A ↦ (inclusion G A).comp f) := by
  intro f h he
  apply RingHom.ext
  intro r
  exact Subtype.ext (congrArg (fun k : R →+* A ↦ k r) he)

/-- The ring factorization is unique, the affine quotient's coordinate universal property. -/
theorem existsUnique_lift (f : R →+* A) (hf : ∀ (g : G) r, g • f r = f r) :
    ∃! h : R →+* invariantRing G A, (inclusion G A).comp h = f := by
  refine ⟨lift G A f hf, rfl, fun h hh ↦ ?_⟩
  exact inclusion_comp_injective G A (hh.trans (inclusion_comp_lift G A f hf).symm)

/-- A finite group makes the actual invariant coordinate inclusion integral. -/
theorem inclusion_isIntegral [Finite G] : (inclusion G A).IsIntegral :=
  (Algebra.IsInvariant.isIntegral (invariantRing G A) A G).isIntegral

end FLT.Mazur.FiniteGroupQuotient
