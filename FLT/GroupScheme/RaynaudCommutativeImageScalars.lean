/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudSimpleScalarField

/-!
# Scalar fields from commutative automorphism images

The acting group need not be commutative. Passing to its actual image
preserves all subrepresentations and hence irreducibility.
-/

@[expose] public noncomputable section

namespace Representation

universe u v w
variable {k : Type u} [Field k] {G : Type w} [Group G]
  {V : Type v} [AddCommGroup V] [Module k V] [Finite V]
  (ρ : Representation k G V) [IsIrreducible ρ]

/-- A simple finite representation with commuting image has a constructed scalar field. -/
theorem exists_rank_one_scalar_field_of_commuting
    (hcomm : ∀ g h : G, Commute (ρ g) (ρ h)) (p : ℕ) [CharP k p] :
    ∃ (F : Type v) (_ : Field F) (_ : Finite F) (_ : CharP F p) (_ : Module F V),
      Module.finrank F V = 1 ∧ ∀ (a : F) (g : G) (x : V), ρ g (a • x) = a • ρ g x := by
  let H := ρ.toHomUnits.range
  let : CommGroup H := { (inferInstance : Group H) with
    mul_comm := by
      rintro ⟨_, ⟨g, rfl⟩⟩ ⟨_, ⟨h, rfl⟩⟩
      apply Subtype.ext
      apply Units.ext
      exact hcomm g h }
  let σ : Representation k H V := (Units.coeHom (Module.End k V)).comp H.subtype
  let e : Subrepresentation σ ≃o Subrepresentation ρ := {
    toFun W := ⟨W.toSubmodule, fun g ↦ W.apply_mem_toSubmodule ⟨ρ.toHomUnits g, ⟨g, rfl⟩⟩⟩
    invFun W := ⟨W.toSubmodule, by
      rintro ⟨_, ⟨g, rfl⟩⟩ x hx
      exact W.apply_mem_toSubmodule g hx⟩
    left_inv _ := rfl
    right_inv _ := rfl
    map_rel_iff' := Iff.rfl }
  let : IsIrreducible σ := e.isSimpleOrder_iff.mpr inferInstance
  obtain ⟨F, hF, hfin, hp, hmod, hdim, hs⟩ := exists_rank_one_scalar_field σ p
  exact ⟨F, hF, hfin, hp, hmod, hdim,
    fun a g x ↦ hs a ⟨ρ.toHomUnits g, ⟨g, rfl⟩⟩ x⟩

end Representation
