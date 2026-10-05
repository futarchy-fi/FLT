/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSectionBaseChange

/-!
# Base change on source opens

Restrict the pullback unit to any open in the source. Its scalar extension
gives a tensor comparison that commutes with source restrictions. These
formulas use the original pullback sheaf and its actual restriction maps.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry Opposite
open Scheme.Modules
open scoped ChangeOfRings

universe u

namespace FLT.Mazur.ModuleSourceSectionBaseChange

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)

/-- The actual structural map to the ring of a source open. -/
def scalarMap (U : X.Opens) : Γ(Y, ⊤) →+* Γ(X, U) :=
  (X.presheaf.map (homOfLE (by simp : U ≤ f ⁻¹ᵁ ⊤)).op).hom.comp f.appTop.hom

/-- Restriction of the pullback unit, with the original base scalars. -/
def unitMap (U : X.Opens) : M.val.obj (op ⊤) ⟶
    (ModuleCat.restrictScalars (scalarMap f U)).obj (((pullback f).obj M).val.obj (op U)) :=
  ModuleCat.ofHom
    (X := M.val.obj (op ⊤))
    (Y := (ModuleCat.restrictScalars (scalarMap f U)).obj
      (((pullback f).obj M).val.obj (op U)))
    { toFun := fun m ↦ ((pullback f).obj M).presheaf.map
        (homOfLE (by simp : U ≤ f ⁻¹ᵁ ⊤)).op
        (((pullbackPushforwardAdjunction f).unit.app M).app ⊤ m)
      map_add' := fun m n ↦ by simp only [map_add]
      map_smul' := fun r m ↦ by
        rw [Hom.app_smul]
        change ((pullback f).obj M).presheaf.map _
          (f.app ⊤ r • (show Γ((pullback f).obj M, f ⁻¹ᵁ ⊤) from
            ((pullbackPushforwardAdjunction f).unit.app M).app ⊤ m)) = _
        rw [map_smul]
        rfl }

/-- Tensor comparison on an arbitrary source open. -/
def comparison (U : X.Opens) :
    (ModuleCat.extendScalars (scalarMap f U)).obj (M.val.obj (op ⊤)) ⟶
      ((pullback f).obj M).val.obj (op U) :=
  ((ModuleCat.extendRestrictScalarsAdj (scalarMap f U)).homEquiv _ _).symm (unitMap f M U)

/-- A unit tensor is the restricted original pullback-unit section. -/
lemma comparison_one_tmul (U : X.Opens) (m : Γ(M, ⊤)) :
    comparison f M U ((1 : Γ(X, U)) ⊗ₜ[Γ(Y, ⊤),scalarMap f U] m) = unitMap f M U m :=
  congrArg (fun k ↦ k m)
    (((ModuleCat.extendRestrictScalarsAdj (scalarMap f U)).homEquiv _ _).apply_symm_apply
      (unitMap f M U))

/-- Pure tensors multiply the restricted pullback unit by the source scalar. -/
lemma comparison_tmul (U : X.Opens) (r : Γ(X, U)) (m : Γ(M, ⊤)) :
    comparison f M U (r ⊗ₜ[Γ(Y, ⊤),scalarMap f U] m) =
      r • (show Γ((pullback f).obj M, U) from unitMap f M U m) := by
  have h := (comparison f M U).hom.map_smul r
    (show (ModuleCat.extendScalars (scalarMap f U)).obj (M.val.obj (op ⊤)) from
      (1 : Γ(X, U)) ⊗ₜ[Γ(Y, ⊤),scalarMap f U] m)
  rw [ModuleCat.ExtendScalars.smul_tmul, mul_one, comparison_one_tmul] at h
  exact h

/-- The unit section commutes with every source-open restriction. -/
lemma unitMap_restrict {U V : X.Opens} (i : U ⟶ V) (m : Γ(M, ⊤)) :
    ((pullback f).obj M).presheaf.map i.op (unitMap f M V m) = unitMap f M U m := by
  change ((pullback f).obj M).presheaf.map i.op
    (((pullback f).obj M).presheaf.map _ _) = _
  rw [← Functor.map_comp_apply]
  rfl

/-- Pure-tensor comparisons retain the original source-chart restriction maps. -/
lemma comparison_restrict {U V : X.Opens} (i : U ⟶ V)
    (r : Γ(X, V)) (m : Γ(M, ⊤)) :
    ((pullback f).obj M).presheaf.map i.op
      (comparison f M V (r ⊗ₜ[Γ(Y, ⊤),scalarMap f V] m)) =
    comparison f M U ((X.presheaf.map i.op r) ⊗ₜ[Γ(Y, ⊤),scalarMap f U] m) := by
  rw [comparison_tmul, comparison_tmul, map_smul, unitMap_restrict]

end FLT.Mazur.ModuleSourceSectionBaseChange
