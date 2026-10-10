/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GlobalIdealPowerCompatibility
public import FLT.Mazur.ModuleCohomology

/-!
# Scalar multiplication lifted to an ideal-action image

A global scalar whose affine restrictions lie in the ideal acts through the
actual ideal multiple. On cohomology this factorization induces the original
scalar action, rather than a separately transported action.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Scheme.Modules FLT.Mazur.FCurve FLT.Mazur.GlobalIdealPower
open FLT.Mazur.GlobalIdealPowerCompatibility

universe u

namespace FLT.Mazur.IdealPowerScalarLift

local instance scalarHasExt (X : Scheme.{u}) :
    HasExt.{u + 1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
  HasExt.standard _

variable {X : Scheme.{u}}

/-- Global scalar multiplication as a morphism of module sheaves. -/
def scalarEnd (M : X.Modules) (r : Γ(X, ⊤)) : M ⟶ M :=
  ⟨PresheafOfModules.homMk (moduleMultiply M r).hom (fun U a x ↦ by
    change Γ(X, U.unop) at a
    change Γ(M, U.unop) at x
    change (X.presheaf.map U.unop.leTop.op r) • (a • x) =
      a • ((X.presheaf.map U.unop.leTop.op r) • x)
    exact smul_comm _ _ _)⟩

/-- Scalar multiplication retains its formula on every open. -/
lemma scalarEnd_app (M : X.Modules) (r : Γ(X, ⊤)) (U : X.Opens) (x : Γ(M, U)) :
    (scalarEnd M r).app U x = X.presheaf.map U.leTop.op r • x := rfl

/-- Forgetting the linear structure recovers the action used to define cohomology. -/
lemma scalarEnd_toSheaf (M : X.Modules) (r : Γ(X, ⊤)) :
    (SheafOfModules.toSheaf X.ringCatSheaf).map (scalarEnd M r) = moduleMultiply M r := rfl

/-- Cohomology of scalar multiplication is precisely the original scalar action. -/
lemma scalarEnd_cohomology (M : X.Modules) (r : Γ(X, ⊤)) (q : ℕ) (x : ModuleH M q) :
    moduleHMap (scalarEnd M r) q x = r • x := rfl

variable [IsLocallyNoetherian X] (I : X.IdealSheafData)
  (M : X.Modules) [M.IsFinitePresentation] (r : Γ(X, ⊤))
  (hr : ∀ U : X.affineOpens, X.presheaf.map U.1.leTop.op r ∈ I.ideal U)

/-- Affine ideal membership factors scalar multiplication through its actual image sheaf. -/
def scalarLift : M ⟶ multiple I M :=
  affineFactor (scalarEnd M r) (inclusion I M) (fun U ↦ by
    rintro _ ⟨x, rfl⟩
    rw [inclusion_range]
    exact Submodule.smul_mem_smul (hr U) Submodule.mem_top)

/-- The scalar lift factors the original multiplication morphism. -/
@[reassoc (attr := simp)]
lemma scalarLift_inclusion : scalarLift I M r hr ≫ inclusion I M = scalarEnd M r :=
  affineFactor_comp _ _ _

/-- The induced cohomology lift maps back to the original scalar multiple. -/
lemma scalarLift_cohomology (q : ℕ) (x : ModuleH M q) :
    moduleHMap (inclusion I M) q (moduleHMap (scalarLift I M r hr) q x) = r • x := by
  rw [← LinearMap.comp_apply, ← moduleHMap_comp, scalarLift_inclusion]
  exact scalarEnd_cohomology M r q x

end FLT.Mazur.IdealPowerScalarLift
