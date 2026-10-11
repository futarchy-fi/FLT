/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleDirectImageHZero
public import FLT.Mazur.SealedLineRestriction

/-!
# Linear H0 restriction along a commuting triangle

The sealed geometric restriction induces a field-linear map between the actual
source cohomology spaces. Its section formula fixes the map without expanding
pullback tensors or adjunctions in its consumers.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Modules

universe u

namespace FLT.Mazur.LinePullbackRestriction

open FCurve

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {K : Type u} [Field K] {X Y Z : Over (Spec (.of K))}
  (s : X ⟶ Y) (p : Y ⟶ Z) (q : X ⟶ Z) (w : s ≫ p = q) (L : Z.left.Modules)

/-- Field-linear restriction on the actual H0 of the two pullback coefficients. -/
def h0Along :
    ModuleScalarH Y.hom ((pullback p.left).obj L) 0 →ₗ[K]
      ModuleScalarH X.hom ((pullback q.left).obj L) 0 :=
  (moduleDirectImageH0Equiv q.left Z.hom X.hom q.w _).toLinearMap.comp
    ((moduleScalarHMap Z.hom (sealedAlong s.left p.left q.left
      (congrArg Over.Hom.left w) L) 0).comp
        (moduleDirectImageH0Equiv p.left Z.hom Y.hom p.w _).symm.toLinearMap)

/-- Taking sections identifies the linear map with the original geometric restriction. -/
theorem h0Along_sections (x : ModuleScalarH Y.hom ((pullback p.left).obj L) 0) :
    moduleScalarH0Equiv X.hom _ (h0Along s p q w L x) =
      (sealedAlong s.left p.left q.left (congrArg Over.Hom.left w) L).app ⊤
        (moduleScalarH0Equiv Y.hom _ x) := by
  have hs := moduleDirectImageH0Equiv_sections p.left Z.hom Y.hom p.w
    ((pullback p.left).obj L)
    ((moduleDirectImageH0Equiv p.left Z.hom Y.hom p.w _).symm x)
  rw [LinearEquiv.apply_symm_apply] at hs
  change moduleScalarH0Equiv _ _ (moduleDirectImageH0Equiv _ _ _ q.w _ _) = _
  rw [moduleDirectImageH0Equiv_sections, LinearMap.comp_apply,
    LinearEquiv.coe_coe, moduleScalarH0Equiv_naturality, ← hs]

end FLT.Mazur.LinePullbackRestriction
