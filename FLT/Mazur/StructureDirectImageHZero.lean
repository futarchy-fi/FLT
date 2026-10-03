/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonBranchDifferenceSheaf
public import FLT.Mazur.ModuleCohomology
/-!
# Degree-zero cohomology of a structure-sheaf direct image

The global-section comparison respects the base-field action through the
composite structure morphism. It needs no separatedness hypothesis.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
@[expose] public noncomputable section
universe u
namespace FLT.Mazur.StructureDirectImage
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open FCurve
variable {K : Type u} [Field K] {X Y : Scheme.{u}}
  (p : X ⟶ Y) (g : Y ⟶ Spec (.of K))
/-- Degree-zero direct-image cohomology is the source section module over the base field. -/
def h0Sections :
    letI := Module.compHom Γ(X, ⊤) (structureScalarMap (p ≫ g))
    ModuleScalarH g (image p) 0 ≃ₗ[K] Γ(X, ⊤) := by
  letI := Module.compHom Γ(X, ⊤) (structureScalarMap (p ≫ g))
  let φ : ModuleH (image p) 0 ≃+ Γ(X, ⊤) := (moduleH0Equiv (image p)).toAddEquiv
  refine { toAddEquiv := φ, map_smul' := ?_ }
  intro a x
  change ModuleH (image p) 0 at x
  have he := (moduleH0Equiv (image p)).map_smul (structureScalarMap g a) x
  have hs : structureScalarMap (p ≫ g) a = p.appTop (structureScalarMap g a) := by
    simp [structureScalarMap]
  change φ ((structureScalarMap g a) • x) = structureScalarMap (p ≫ g) a * φ x
  rw [hs]
  exact he
end FLT.Mazur.StructureDirectImage
