/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleCohomology
public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Linear degree-zero direct-image comparison

Global sections of an arbitrary module direct image are its source sections.
The comparison retains the field action through a specified commuting triangle;
no affine, proper, or acyclicity hypothesis is needed in degree zero.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Modules

universe u

namespace FLT.Mazur.FCurve

set_option backward.isDefEq.respectTransparency false

variable {K : Type u} [Field K] {X Y : Scheme.{u}}
  (p : X ⟶ Y) (g : Y ⟶ Spec (.of K)) (f : X ⟶ Spec (.of K)) (w : p ≫ g = f)
  (M : X.Modules)

/-- Direct-image H0 is linearly the source H0 with its specified structure morphism. -/
def moduleDirectImageH0Equiv :
    ModuleScalarH g ((pushforward p).obj M) 0 ≃ₗ[K] ModuleScalarH f M 0 := by
  let _ := Module.compHom (M.val.obj (op ⊤)) (structureScalarMap f)
  let φ : ModuleScalarH g ((pushforward p).obj M) 0 ≃+ M.val.obj (op ⊤) :=
    (moduleH0Equiv ((pushforward p).obj M)).toAddEquiv
  let e : ModuleScalarH g ((pushforward p).obj M) 0 ≃ₗ[K] M.val.obj (op ⊤) :=
    { toAddEquiv := φ
      map_smul' := by
        intro a x
        change ModuleH ((pushforward p).obj M) 0 at x
        have he := (moduleH0Equiv ((pushforward p).obj M)).map_smul
          (structureScalarMap g a) x
        have hs : structureScalarMap f a = p.appTop (structureScalarMap g a) := by
          rw [← w]
          simp [structureScalarMap]
        change φ (structureScalarMap g a • x) = structureScalarMap f a • φ x
        rw [hs]
        exact he }
  exact e.trans (moduleScalarH0Equiv f M).symm

/-- The linear comparison preserves the actual global section. -/
theorem moduleDirectImageH0Equiv_sections
    (x : ModuleScalarH g ((pushforward p).obj M) 0) :
    moduleScalarH0Equiv f M (moduleDirectImageH0Equiv p g f w M x) =
      moduleScalarH0Equiv g ((pushforward p).obj M) x :=
  (moduleH0Equiv M).apply_symm_apply _

/-- Transporting coefficients before direct image commutes with the H0 comparison. -/
theorem moduleDirectImageH0Equiv_naturality {N : X.Modules} (e : M ⟶ N)
    (x : ModuleScalarH g ((pushforward p).obj M) 0) :
    moduleDirectImageH0Equiv p g f w N
        (moduleScalarHMap g ((pushforward p).map e) 0 x) =
      moduleScalarHMap f e 0 (moduleDirectImageH0Equiv p g f w M x) := by
  apply (moduleScalarH0Equiv f N).injective
  rw [moduleDirectImageH0Equiv_sections, moduleScalarH0Equiv_naturality,
    moduleScalarH0Equiv_naturality, moduleDirectImageH0Equiv_sections]
  rfl

end FLT.Mazur.FCurve
