/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalScalarRelationLiftIdeal
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Full relation numerators as an original scalar module

The full equalizer is closed under original scalars. Its boundary image and
cokernel therefore record the exact obstruction without replacing the source
prime or discarding residual relation equations.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.OriginalScalarRelationModule
variable {R A B C : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R B] (β : A →ₐ[R] B) (F H : A →+* C)
  (hσ : ∀ r, F (algebraMap R A r) = H (algebraMap R A r))

/-- The full relation equalizer, as a module over the unchanged scalar ring. -/
def compatible : Submodule R A where
  carrier := {w | F w = H w}
  zero_mem' := by simp
  add_mem' := by
    intro u v hu hv
    simp only [Set.mem_ofPred_eq, map_add] at *
    rw [hu, hv]
  smul_mem' := by
    intro r w hw
    change F (r • w) = H (r • w)
    rw [Algebra.smul_def, map_mul, map_mul, hσ, hw]

/-- The exact boundary map on full-relation-compatible numerators. -/
def boundaryMap : compatible F H hσ →ₗ[R] B :=
  β.toLinearMap.comp (compatible F H hσ).subtype

/-- The obstruction is the class in the actual compatible boundary cokernel. -/
def obstruction (t : B) : B ⧸ LinearMap.range (boundaryMap β F H hσ) :=
  Submodule.Quotient.mk t

/-- An obstruction vanishes precisely when there is an exact compatible boundary lift. -/
theorem obstruction_eq_zero (t : B) : obstruction β F H hσ t = 0 ↔
    ∃ w : A, β w = t ∧ F w = H w := by
  rw [obstruction, Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨w.val, hw, w.property⟩
  · rintro ⟨w, hw, he⟩
    exact ⟨⟨w, he⟩, hw⟩

/-- The original lift ideal is exactly the scalar annihilator of this boundary obstruction. -/
theorem smul_obstruction_eq_zero (r : R) (t : B) :
    r • obstruction β F H hσ t = 0 ↔
      r ∈ OriginalScalarRelationLiftIdeal.liftIdeal (algebraMap R A) β.toRingHom F H hσ t := by
  change obstruction β F H hσ (r • t) = 0 ↔ _
  rw [obstruction_eq_zero, OriginalScalarRelationLiftIdeal.mem_liftIdeal]
  simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, AlgHom.commutes,
    Algebra.smul_def]

end FLT.Mazur.OriginalScalarRelationModule
