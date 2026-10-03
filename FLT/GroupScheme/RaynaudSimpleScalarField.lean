/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudSimpleEndomorphismField
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.Algebra.CharP.Algebra

/-!
# Finite scalar fields for simple commutative representations

The scalar field is constructed from the actual endomorphisms. Its rank and
commutation with the action are proved, not supplied as representation data.
-/

@[expose] public noncomputable section

namespace Representation
open scoped MonoidAlgebra
open ThreeAdicPlan

universe u v w
variable {k : Type u} [Field k] {G : Type w} [CommMonoid G]
  {V : Type v} [AddCommGroup V] [Module k V] [Finite V]
  (ρ : Representation k G V) [IsIrreducible ρ]

/-- A finite simple commutative representation is a line over its actual scalar field. -/
theorem exists_rank_one_scalar_field (p : ℕ) [CharP k p] :
    ∃ (F : Type v) (_ : Field F) (_ : Finite F) (_ : CharP F p) (_ : Module F V),
      Module.finrank F V = 1 ∧ ∀ (a : F) (g : G) (x : V), ρ g (a • x) = a • ρ g x := by
  let : Finite ρ.asModule := Finite.of_equiv V ρ.asModuleEquiv.toEquiv.symm
  let F := SimpleScalarField k[G] ρ.asModule
  let e := ρ.asModuleEquiv.symm.toAddEquiv
  let : Module F V := e.module F
  let f : k →+* F := Module.toModuleEnd k[G] ρ.asModule
  let : CharP F p := charP_of_injective_ringHom f.injective p
  refine ⟨F, inferInstance, inferInstance, inferInstance, inferInstance, ?_, ?_⟩
  · exact (e.linearEquiv F).finrank_eq.trans (simpleScalarField_finrank k[G] ρ.asModule)
  · intro a g x
    apply e.injective
    change ρ.asModuleEquiv.symm (ρ g (a • x)) = _
    rw [asModuleEquiv_symm_map_rho]
    have hs (y : V) : e (a • y) = a • e y := (e.linearEquiv F).map_smul a y
    rw [show ρ.asModuleEquiv.symm (a • x) = a • e x from hs x, hs]
    let a' : Module.End k[G] ρ.asModule := a
    change MonoidAlgebra.of k G g • a' (e x) = a' (e (ρ g x))
    rw [show e (ρ g x) = MonoidAlgebra.of k G g • e x from
      asModuleEquiv_symm_map_rho ρ g x]
    exact (a'.map_smul _ _).symm

end Representation
