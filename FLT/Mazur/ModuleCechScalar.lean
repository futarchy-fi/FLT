/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CechAcyclicNaturality

/-!
# Scalars on Cech cohomology

Multiplication on the coefficient sheaf induces the global-section action on
Cech cohomology. Naturality makes the acyclic-cover comparison linear, also
after restricting scalars along a structure morphism.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace FLT.Mazur.CechSheafHZero

variable {X : TopCat.{u}} {ι : Type u} (U : ι → Opens X)

/-- The Cech construction is additive in the coefficient presheaf. -/
instance cechComplexFunctor_additive :
    (cechComplexFunctor (A := AddCommGrpCat.{u}) U).Additive where
  map_add := by
    intro F G f g
    ext n : 1
    change Limits.Pi.map (fun b : Fin (n + 1) → ι ↦ (f + g).app (op (∏ᶜ (U ∘ b)))) =
      Limits.Pi.map (fun b ↦ f.app (op (∏ᶜ (U ∘ b)))) +
        Limits.Pi.map (fun b ↦ g.app (op (∏ᶜ (U ∘ b))))
    apply Pi.hom_ext
    intro a
    simp only [Preadditive.add_comp, Pi.map_π, NatTrans.app_add, Preadditive.comp_add]

/-- Addition of coefficient maps induces addition on Cech cohomology. -/
lemma chMap_add {F G : TopCat.Sheaf AddCommGrpCat.{u} X} (f g : F ⟶ G) (n : ℕ) :
    CHmap U (f + g) n = CHmap U f n + CHmap U g n := by
  change HomologicalComplex.homologyMap ((cechComplexFunctor U).map (f.hom + g.hom)) n = _
  rw [Functor.map_add, HomologicalComplex.homologyMap_add]

/-- Composition of coefficient maps induces composition on Cech cohomology. -/
lemma chMap_comp {F G H : TopCat.Sheaf AddCommGrpCat.{u} X}
    (f : F ⟶ G) (g : G ⟶ H) (n : ℕ) :
    CHmap U (f ≫ g) n = CHmap U f n ≫ CHmap U g n := by
  change HomologicalComplex.homologyMap ((cechComplexFunctor U).map (f.hom ≫ g.hom)) n = _
  rw [Functor.map_comp, HomologicalComplex.homologyMap_comp]

end FLT.Mazur.CechSheafHZero

namespace FLT.Mazur.FCurve

open CechSheafHZero CechAcyclicCokernel CechAcyclicComparison CechAcyclicNaturality

local instance moduleCechHasExt (Y : Scheme.{u}) :
    HasExt.{u + 1} (Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}) :=
  HasExt.standard _

variable {Y : Scheme.{u}} {ι : Type u} (M : Y.Modules) (W : ι → Opens Y)

/-- The action is constructed from coefficient maps independently of any comparison. -/
def moduleCechAction (n : ℕ) :
    Γ(Y, ⊤) →+* AddMonoid.End (CH W (moduleAbelianSheaf M) n) where
  toFun r := (CHmap W (moduleMultiply M r) n).hom
  map_one' := by
    ext x
    exact congrArg (fun f ↦ CHmap W f n x) (moduleMultiply_one M) |>.trans
      (chMap_id_apply W _ n x)
  map_mul' r s := by
    ext x
    change CHmap W (moduleMultiply M (r * s)) n x =
      CHmap W (moduleMultiply M r) n (CHmap W (moduleMultiply M s) n x)
    rw [moduleMultiply_mul, chMap_comp]
    rfl
  map_add' r s := by
    ext x
    change CHmap W (moduleMultiply M (r + s)) n x = _
    rw [moduleMultiply_add, chMap_add]
    rfl
  map_zero' := by
    have h : moduleMultiply M 0 = 0 := by
      apply add_left_cancel (a := moduleMultiply M 0)
      simpa using (moduleMultiply_add M 0 0).symm
    ext x
    change CHmap W (moduleMultiply M 0) n x = 0
    simp [h, CHmap]

/-- Global sections act through multiplication on the coefficient sheaf. -/
instance moduleCechModule (n : ℕ) : Module Γ(Y, ⊤) (CH W (moduleAbelianSheaf M) n) :=
  Module.compHom _ (moduleCechAction M W n)

/-- Expose the same scalar action on the underlying Ext cohomology type. -/
local instance moduleCechExtModule (n : ℕ) :
    Module Γ(Y, ⊤) (Sheaf.H (moduleAbelianSheaf M) n) := moduleHModule M n

variable (hW : iSup W = ⊤) (hM : CoverAcyclic W (moduleAbelianSheaf M))

/-- Naturality identifies coefficient multiplication with the Ext scalar action. -/
lemma acyclicCoverEquiv_multiply (r : Γ(Y, ⊤)) (n : ℕ)
    (x : CH W (moduleAbelianSheaf M) n) :
    acyclicCoverEquiv W hW _ hM n (CHmap W (moduleMultiply M r) n x) =
      r • (acyclicCoverEquiv W hW _ hM n x : ModuleH M n) :=
  acyclicCoverEquiv_naturality W hW hM hM (moduleMultiply M r) n x

/-- The comparison for an acyclic cover is linear over global sections. -/
def moduleCechEquiv (n : ℕ) :
    CH W (moduleAbelianSheaf M) n ≃ₗ[Γ(Y, ⊤)] ModuleH M n where
  toAddEquiv := acyclicCoverEquiv W hW _ hM n
  map_smul' r x := acyclicCoverEquiv_multiply M W hW hM r n x

/-- Restriction along the structure morphism gives the comparison over the base field. -/
def moduleScalarCechEquiv {k : Type u} [Field k]
    (f : Y ⟶ Spec (CommRingCat.of k)) (n : ℕ) :
    letI := Module.compHom (CH W (moduleAbelianSheaf M) n) (structureScalarMap f)
    CH W (moduleAbelianSheaf M) n ≃ₗ[k] ModuleScalarH f M n := by
  letI := Module.compHom (CH W (moduleAbelianSheaf M) n) (structureScalarMap f)
  exact
    { toAddEquiv := (moduleCechEquiv M W hW hM n).toAddEquiv
      map_smul' := fun a x ↦
        ((moduleCechEquiv M W hW hM n).map_smul (structureScalarMap f a) x).trans
          (moduleScalarH_smul f M n a ((moduleCechEquiv M W hW hM n) x)).symm }

end FLT.Mazur.FCurve
