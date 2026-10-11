/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Extension.Basic

/-!
# The original conormal is unchanged by infinitesimalization

The genuine extension map from a presentation to its quotient by the square
of the relation ideal induces an isomorphism of conormals over the target.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.InfinitesimalConormalEquiv

open Algebra.Extension

set_option backward.isDefEq.respectTransparency false

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  (P : Algebra.Extension R A)

/-- The infinitesimal relation ideal is square-zero. -/
theorem ker_square : P.infinitesimal.ker ^ 2 = ⊥ := by
  rw [Algebra.Extension.ker_infinitesimal, Ideal.cotangentIdeal_square]

/-- No original conormal class is lost by passing to the infinitesimal presentation. -/
theorem map_injective : Function.Injective (Cotangent.map P.toInfinitesimal) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  obtain ⟨x, rfl⟩ := Cotangent.mk_surjective x
  rw [Cotangent.map_mk, Cotangent.mk_eq_zero_iff, ker_square, Submodule.mem_bot] at hx
  rw [Cotangent.mk_eq_zero_iff]
  exact Ideal.Quotient.eq_zero_iff_mem.mp hx

/-- Every infinitesimal conormal class comes from the original conormal. -/
theorem map_surjective : Function.Surjective (Cotangent.map P.toInfinitesimal) := by
  intro y
  obtain ⟨y, rfl⟩ := Cotangent.mk_surjective y
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective y.val
  have hmem : x ∈ P.ker := by
    have hy := y.property
    rw [← hx] at hy
    exact hy
  refine ⟨Cotangent.mk ⟨x, hmem⟩, ?_⟩
  rw [Cotangent.map_mk]
  congr 1
  exact Subtype.ext hx

/-- The genuine infinitesimal extension map identifies original conormals over the target. -/
def equiv : P.Cotangent ≃ₗ[A] P.infinitesimal.Cotangent :=
  LinearEquiv.ofBijective (Cotangent.map P.toInfinitesimal)
    ⟨map_injective P, map_surjective P⟩

/-- The equivalence retains the actual map on relation representatives. -/
@[simp] theorem equiv_mk (x : P.ker) :
    equiv P (Cotangent.mk x) = Cotangent.mk
      ⟨P.toInfinitesimal.toAlgHom x, by
        change algebraMap P.Ring A x.val = 0
        exact x.property⟩ := rfl

end FLT.Mazur.InfinitesimalConormalEquiv
