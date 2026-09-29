/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CechSortingMaps
public import FLT.Mazur.ModuleCechScalar

/-!
# Linear Cech terms

Coefficient multiplication acts on the actual categorical Cech terms. Their
section coordinates are linear, and are finite products when the cover index
is finite. The differentials are linear over any ring mapping to global sections.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u v

namespace FLT.Mazur.FCurve

open CechSheafHZero

variable {X : Scheme.{u}} {ι : Type u} (M : X.Modules) (U : ι → X.Opens)

/-- Coefficient multiplication on a categorical Cech term. -/
def finiteCechTermAction (n : ℕ) :
    Γ(X, ⊤) →+* AddMonoid.End ((C U (moduleAbelianSheaf M)).X n) where
  toFun r := (((cechComplexFunctor U).map (moduleMultiply M r).hom).f n).hom
  map_one' := by
    ext x
    simp only [moduleMultiply_one]
    change (((cechComplexFunctor U).map (𝟙 (moduleAbelianSheaf M).obj)).f n).hom x = x
    rw [CategoryTheory.Functor.map_id]
    rfl
  map_mul' r s := by
    ext x
    rw [moduleMultiply_mul]
    change (((cechComplexFunctor U).map
      ((moduleMultiply M s).hom ≫ (moduleMultiply M r).hom)).f n).hom x = _
    rw [Functor.map_comp]
    rfl
  map_add' r s := by
    ext x
    rw [moduleMultiply_add]
    change (((cechComplexFunctor U).map
      ((moduleMultiply M r).hom + (moduleMultiply M s).hom)).f n).hom x = _
    rw [Functor.map_add]
    rfl
  map_zero' := by
    have h : moduleMultiply M 0 = 0 := by
      apply add_left_cancel (a := moduleMultiply M 0)
      simpa using (moduleMultiply_add M 0 0).symm
    ext x
    simp [h]

/-- The term action comes directly from coefficient multiplication. -/
instance finiteCechTermModule (n : ℕ) :
    Module Γ(X, ⊤) ((C U (moduleAbelianSheaf M)).X n) :=
  Module.compHom _ (finiteCechTermAction M U n)

lemma finiteCechTerm_smul (n : ℕ) (r : Γ(X, ⊤))
    (x : (C U (moduleAbelianSheaf M)).X n) :
    r • x = ((cechComplexFunctor U).map (moduleMultiply M r).hom).f n x := rfl

/-- Global sections act on intersection sections by restriction. -/
local instance finiteCechSectionModule (W : X.Opens) :
    Module Γ(X, ⊤) ((moduleAbelianSheaf M).obj.obj (op W)) :=
  Module.compHom (M.val.obj (op W)) (X.presheaf.map (homOfLE (show W ≤ ⊤ from le_top)).op).hom

/-- The categorical term is linearly the product of its intersection sections. -/
def finiteCechTermEquiv (n : ℕ) :
    (C U (moduleAbelianSheaf M)).X n ≃ₗ[Γ(X, ⊤)]
      (∀ a : Fin (n + 1) → ι, (moduleAbelianSheaf M).obj.obj (op (V U n a))) where
  toAddEquiv := termEquiv U (moduleAbelianSheaf M) n
  map_smul' r x := by
    funext a
    exact CechSortingMaps.termEquiv_naturality U (moduleMultiply M r) n x a

/-- For a finite cover, every coordinate product has a finite index set. -/
lemma finiteCechTerm_index_finite [Finite ι] (n : ℕ) :
    Finite (Fin (n + 1) → ι) := inferInstance

/-- All differentials commute with the coefficient scalar action. -/
lemma finiteCech_d_smul (i j : ℕ) (r : Γ(X, ⊤))
    (x : (C U (moduleAbelianSheaf M)).X i) :
    (C U (moduleAbelianSheaf M)).d i j (r • x) =
      r • (C U (moduleAbelianSheaf M)).d i j x := by
  exact ConcreteCategory.congr_hom
    (((cechComplexFunctor U).map (moduleMultiply M r).hom).comm i j) x

/-- The actual categorical differential as a linear map. -/
def finiteCechDifferential (i j : ℕ) :
    (C U (moduleAbelianSheaf M)).X i →ₗ[Γ(X, ⊤)]
      (C U (moduleAbelianSheaf M)).X j where
  toAddHom := ((C U (moduleAbelianSheaf M)).d i j).hom
  map_smul' := finiteCech_d_smul M U i j

variable {R : Type v} [Ring R] (ρ : R →+* Γ(X, ⊤))

/-- Coordinates remain linear over any chosen base ring. -/
def finiteCechRingTermEquiv (n : ℕ) :
    letI _termModule := Module.compHom ((C U (moduleAbelianSheaf M)).X n) ρ
    letI _sectionModule := fun a : Fin (n + 1) → ι ↦
      Module.compHom ((moduleAbelianSheaf M).obj.obj (op (V U n a))) ρ
    (C U (moduleAbelianSheaf M)).X n ≃ₗ[R]
      (∀ a : Fin (n + 1) → ι, (moduleAbelianSheaf M).obj.obj (op (V U n a))) := by
  letI _termModule := Module.compHom ((C U (moduleAbelianSheaf M)).X n) ρ
  letI _sectionModule := fun a : Fin (n + 1) → ι ↦
    Module.compHom ((moduleAbelianSheaf M).obj.obj (op (V U n a))) ρ
  exact
    { toAddEquiv := termEquiv U (moduleAbelianSheaf M) n
      map_smul' := fun r x ↦ (finiteCechTermEquiv M U n).map_smul (ρ r) x }

/-- Every differential is linear over the chosen base ring. -/
def finiteCechRingDifferential (i j : ℕ) :
    letI _sourceModule := Module.compHom ((C U (moduleAbelianSheaf M)).X i) ρ
    letI _targetModule := Module.compHom ((C U (moduleAbelianSheaf M)).X j) ρ
    (C U (moduleAbelianSheaf M)).X i →ₗ[R] (C U (moduleAbelianSheaf M)).X j := by
  letI _sourceModule := Module.compHom ((C U (moduleAbelianSheaf M)).X i) ρ
  letI _targetModule := Module.compHom ((C U (moduleAbelianSheaf M)).X j) ρ
  exact
    { toAddHom := ((C U (moduleAbelianSheaf M)).d i j).hom
      map_smul' := fun r x ↦ finiteCech_d_smul M U i j (ρ r) x }

end FLT.Mazur.FCurve
