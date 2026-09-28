/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ScalarCohomology
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# The constant-sections condition for curve genus

The hypothesis `H⁰(X, O_X) = k` in Stacks 0BY7 means that the canonical scalar map
on global sections is bijective. We express this using the specified structure morphism
and prove that the actual degree-zero cohomology is finite-dimensional of dimension one.

This is the degree-zero part of FC08. Defining genus still requires a geometric proof of
finite-dimensionality of `H1 f`, as in Stacks 02O6. No genus is defined here.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace FLT.Mazur.FCurve

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- The canonical map from the base field to global functions is an isomorphism. -/
def HasConstantGlobalSections (f : X ⟶ Spec (CommRingCat.of k)) : Prop :=
  Function.Bijective (structureScalarMap f)

/-- The canonical scalar map viewed as a linear map for the base-field action. -/
def globalSectionsScalarLinearMap (f : X ⟶ Spec (CommRingCat.of k)) :
    letI := Module.compHom Γ(X, ⊤) (structureScalarMap f)
    k →ₗ[k] Γ(X, ⊤) := by
  letI := Module.compHom Γ(X, ⊤) (structureScalarMap f)
  exact
    { toFun := structureScalarMap f
      map_add' := (structureScalarMap f).map_add
      map_smul' := (structureScalarMap f).map_mul }

/-- The canonical inclusion of constants into degree-zero cohomology. -/
def scalarH0Constants (f : X ⟶ Spec (CommRingCat.of k)) : k →ₗ[k] H0 f := by
  letI := Module.compHom Γ(X, ⊤) (structureScalarMap f)
  exact (scalarH0Equiv f).symm.toLinearMap.comp (globalSectionsScalarLinearMap f)

/-- The comparison with global sections sends a constant to its scalar section. -/
@[simp]
lemma scalarH0Equiv_constants (f : X ⟶ Spec (CommRingCat.of k)) (a : k) :
    scalarH0Equiv f (scalarH0Constants f a) = structureScalarMap f a := by
  let := Module.compHom Γ(X, ⊤) (structureScalarMap f)
  exact (scalarH0Equiv f).apply_symm_apply _

/-- The global-functions condition is exactly bijectivity of the canonical constants map. -/
lemma hasConstantGlobalSections_iff (f : X ⟶ Spec (CommRingCat.of k)) :
    HasConstantGlobalSections f ↔ Function.Bijective (scalarH0Constants f) := by
  let := Module.compHom Γ(X, ⊤) (structureScalarMap f)
  change Function.Bijective (structureScalarMap f) ↔
    Function.Bijective ((scalarH0Equiv f).symm ∘ structureScalarMap f)
  exact ((scalarH0Equiv f).symm.bijective.of_comp_iff' _).symm

/-- Constant global functions identify the base field with the actual zeroth cohomology. -/
def scalarH0ConstantsEquiv (f : X ⟶ Spec (CommRingCat.of k))
    (h : HasConstantGlobalSections f) : k ≃ₗ[k] H0 f :=
  LinearEquiv.ofBijective (scalarH0Constants f) ((hasConstantGlobalSections_iff f).mp h)

/-- Finiteness of zeroth cohomology follows from the constant-sections condition. -/
theorem finiteDimensional_H0_of_constantGlobalSections
    (f : X ⟶ Spec (CommRingCat.of k)) (h : HasConstantGlobalSections f) :
    FiniteDimensional k (H0 f) :=
  (scalarH0ConstantsEquiv f h).finiteDimensional

/-- The degree-zero dimension in the curve genus contract is one. -/
theorem finrank_H0_of_constantGlobalSections
    (f : X ⟶ Spec (CommRingCat.of k)) (h : HasConstantGlobalSections f) :
    Module.finrank k (H0 f) = 1 := by
  rw [← (scalarH0ConstantsEquiv f h).finrank_eq, Module.finrank_self]

end FLT.Mazur.FCurve
