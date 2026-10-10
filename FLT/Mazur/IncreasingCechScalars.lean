/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CechSortingHomotopy
public import FLT.Mazur.FiniteCechTermScalars

/-!
# Scalar actions on the bounded Cech complex

The increasing-tuple complex inherits the actual coefficient multiplication
maps. Its differentials and the comparison with the full complex are linear.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

namespace FLT.Mazur.IncreasingCechScalars
open IncreasingCechComplex CechSortingMaps FCurve CechSheafHZero

universe u
variable {X : Scheme.{u}} {ι : Type u} [LinearOrder ι]
  (M : X.Modules) (U : ι → X.Opens)

/-- Coefficient multiplication is a ring action on every increasing Cech term. -/
def termAction (n : ℕ) :
    Γ(X, ⊤) →+* AddMonoid.End (Term U (moduleAbelianSheaf M) n) where
  toFun r := coefficientHom U (moduleMultiply M r) n
  map_one' := by
    ext x a
    change ((moduleMultiply M 1).hom.app _) (x a) = x a
    rw [moduleMultiply_one]
    rfl
  map_mul' r s := by
    ext x a
    change ((moduleMultiply M (r * s)).hom.app _) (x a) =
      ((moduleMultiply M r).hom.app _) (((moduleMultiply M s).hom.app _) (x a))
    rw [moduleMultiply_mul]
    rfl
  map_add' r s := by
    ext x a
    change ((moduleMultiply M (r + s)).hom.app _) (x a) =
      ((moduleMultiply M r).hom.app _) (x a) + ((moduleMultiply M s).hom.app _) (x a)
    rw [moduleMultiply_add]
    rfl
  map_zero' := by
    have h : moduleMultiply M 0 = 0 := by
      apply add_left_cancel (a := moduleMultiply M 0)
      simpa using (moduleMultiply_add M 0 0).symm
    ext x a
    change ((moduleMultiply M 0).hom.app _) (x a) = 0
    rw [h]
    rfl

/-- This module structure uses multiplication on the actual coefficient sheaf. -/
instance termModule (n : ℕ) : Module Γ(X, ⊤) (Term U (moduleAbelianSheaf M) n) :=
  Module.compHom _ (termAction M U n)

/-- The original differential commutes with global scalars. -/
lemma differential_smul (n : ℕ) (r : Γ(X, ⊤))
    (x : Term U (moduleAbelianSheaf M) n) :
    differential U (moduleAbelianSheaf M) n (r • x) =
      r • differential U (moduleAbelianSheaf M) n x :=
  (coefficientHom_differential U (moduleMultiply M r) n x).symm

/-- The bounded differential as a linear map. -/
def linearDifferential (n : ℕ) :
    Term U (moduleAbelianSheaf M) n →ₗ[Γ(X, ⊤)]
      Term U (moduleAbelianSheaf M) (n + 1) where
  toAddHom := differential U (moduleAbelianSheaf M) n
  map_smul' := differential_smul M U n

/-- Restriction from all tuples to increasing tuples respects the actual scalars. -/
def linearRestriction (n : ℕ) :
    (C U (moduleAbelianSheaf M)).X n →ₗ[Γ(X, ⊤)]
      Term U (moduleAbelianSheaf M) n where
  toAddHom := (restrict U (moduleAbelianSheaf M) n).comp
    (termEquiv U (moduleAbelianSheaf M) n).toAddMonoidHom
  map_smul' r x := by
    funext a
    exact termEquiv_naturality U (moduleMultiply M r) n x a.val

/-- The linear differential still squares to zero. -/
lemma linearDifferential_comp (n : ℕ) :
    (linearDifferential M U (n + 1)).comp (linearDifferential M U n) = 0 := by
  apply LinearMap.ext
  intro x
  exact differential_sq U (moduleAbelianSheaf M) n x

/-- The linear terms retain the finite cover's cardinal bound. -/
lemma termModule_subsingleton [Fintype ι] (n : ℕ) (hn : Fintype.card ι ≤ n) :
    Subsingleton (Term U (moduleAbelianSheaf M) n) :=
  term_subsingleton U (moduleAbelianSheaf M) n hn

end FLT.Mazur.IncreasingCechScalars
