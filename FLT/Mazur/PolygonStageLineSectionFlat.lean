/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffinePieceSectionLocalization
public import FLT.Mazur.AmpleAffinePullback
public import FLT.Mazur.FlatLineSectionTerms
public import FLT.Mazur.PolygonInfinitesimalStageLine

/-!
# Actual flat coefficient modules on polygon charts

Sections of every tensor power of the boundary line on an affine open of a
truncated polygon stage are flat over the original truncated polynomial ring.
The scalar action is the actual structural map followed by open restriction.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

open FCurve ModuleLineBundleTensorPullback AffinePieceSectionLocalization

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (R : Type) [CommRing R] (m n : ℕ) (h : 2 ≤ n)

/-- The actual truncated coefficients act on the stage through its structural morphism. -/
def stageScalars : Ring R m →+* Γ((family R m n h).left, ⊤) :=
  affineBaseScalars (family R m n h).hom

/-- Tensor-line sections on an open, with their actual truncated coefficient action. -/
abbrev boundaryPowerSections (d : ℕ) (U : (family R m n h).left.Opens) :
    ModuleCat (Ring R m) :=
  baseSections (tensorPower (boundaryLine R m n h) d) (stageScalars R m n h) U

/-- Every affine chart gives a flat module in every tensor degree. -/
theorem boundaryPowerSections_flat (d : ℕ) (U : (family R m n h).left.Opens)
    (hU : IsAffineOpen U) : Module.Flat (Ring R m) (boundaryPowerSections R m n h d U) := by
  let B := Γ(Spec (.of (Ring R m)), ⊤)
  let e := Scheme.ΓSpecIso (.of (Ring R m))
  let _ : Algebra (Ring R m) B := e.inv.hom.toAlgebra
  let _ : Module.Flat (Ring R m) B :=
    RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso e.inv)
  let N := baseSections (tensorPower (boundaryLine R m n h) d)
    (family R m n h).hom.appTop.hom U
  let _ : Module.Flat B N := FlatLineSectionTerms.affineOpen_flat (family R m n h).hom
    _ ((boundaryLine_rankOne R m n h).tensorPower d) U hU
  let _ : Module (Ring R m) N := Module.compHom N e.inv.hom
  let _ : IsScalarTower (Ring R m) B N :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  exact Module.Flat.trans (Ring R m) B N

end FLT.Mazur.PolygonInfinitesimalStages
