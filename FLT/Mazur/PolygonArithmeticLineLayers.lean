/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticBoundaryLine
public import FLT.Mazur.PolygonArithmeticFlatLayer
public import FLT.Mazur.AffinePieceSectionLocalization
public import FLT.Mazur.AmpleAffinePullback
public import FLT.Mazur.FlatLineSectionTerms

/-!
# Exact coefficient layers on actual arithmetic polygon charts

The original arithmetic structure map makes affine sections of every
boundary-line power flat over the correct quotient ring. Their adjacent
coefficient sequence is therefore short exact and commutes with open
restriction, also when the integral base has mixed characteristic.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonArithmeticStages
open FCurve ModuleLineBundleTensorPullback AffinePieceSectionLocalization
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (A : Type) [CommRing A] (π : A) (m n : ℕ) (h : 2 ≤ n)

/-- The actual arithmetic coefficients act through the unchanged stage structure map. -/
def stageScalars : Quotient A π m →+* Γ((family A π m n h).left, ⊤) :=
  affineBaseScalars (family A π m n h).hom

/-- Actual tensor-line sections with their original arithmetic scalar action. -/
abbrev boundaryPowerSections (d : ℕ) (U : (family A π m n h).left.Opens) :
    ModuleCat (Quotient A π m) :=
  baseSections (tensorPower (boundaryLine A π m n h) d) (stageScalars A π m n h) U

/-- Every affine chart supplies flat section modules in every tensor degree. -/
theorem boundaryPowerSections_flat (d : ℕ) (U : (family A π m n h).left.Opens)
    (hU : IsAffineOpen U) :
    Module.Flat (Quotient A π m) (boundaryPowerSections A π m n h d U) := by
  let B := Γ(Spec (.of (Quotient A π m)), ⊤)
  let e := Scheme.ΓSpecIso (.of (Quotient A π m))
  let _ : Algebra (Quotient A π m) B := e.inv.hom.toAlgebra
  let _ : Module.Flat (Quotient A π m) B :=
    RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso e.inv)
  let N := baseSections (tensorPower (boundaryLine A π m n h) d)
    (family A π m n h).hom.appTop.hom U
  let _ : Module.Flat B N := FlatLineSectionTerms.affineOpen_flat (family A π m n h).hom
    _ ((boundaryLine_rankOne A π m n h).tensorPower d) U hU
  let _ : Module (Quotient A π m) N := Module.compHom N e.inv.hom
  let _ : IsScalarTower (Quotient A π m) B N :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  exact Module.Flat.trans (Quotient A π m) B N

variable [IsDomain A] (hπ : π ≠ 0) (d : ℕ)
  (U : (family A π (m + 1) n h).left.Opens) (hU : IsAffineOpen U)

/-- The exact coefficient complex on actual arithmetic boundary tensor-line sections. -/
def boundaryPowerLayerSequence : ShortComplex (ModuleCat (Quotient A π (m + 1))) :=
  let _ := boundaryPowerSections_flat A π (m + 1) n h d U hU
  flatLayerSequence A π hπ m (boundaryPowerSections A π (m + 1) n h d U)

/-- Flatness proves local exactness without assuming that global sections lift. -/
theorem boundaryPowerLayerSequence_shortExact :
    (boundaryPowerLayerSequence A π m n h hπ d U hU).ShortExact := by
  let _ := boundaryPowerSections_flat A π (m + 1) n h d U hU
  exact flatLayerSequence_shortExact A π hπ m (boundaryPowerSections A π (m + 1) n h d U)

/-- The closed-layer embedding is the original last-power multiplication on sections. -/
theorem boundaryPowerLayerSequence_f_mk
    (s : boundaryPowerSections A π (m + 1) n h d U) :
    (boundaryPowerLayerSequence A π m n h hπ d U hU).f (Submodule.Quotient.mk s) =
      parameter A π (m + 1) ^ (m + 1) • s := rfl

variable {U} {V : (family A π (m + 1) n h).left.Opens} (hV : IsAffineOpen V) (i : U ≤ V)

/-- Open restriction preserves the actual arithmetic closed-layer inclusion. -/
theorem boundaryPowerLayerSequence_restrict :
    let _ := boundaryPowerSections_flat A π (m + 1) n h d U hU
    let _ := boundaryPowerSections_flat A π (m + 1) n h d V hV
    let f := AffinePieceSectionLocalization.baseRestriction
      (tensorPower (boundaryLine A π (m + 1) n h) d) (stageScalars A π (m + 1) n h) i
    f.comp (boundaryPowerLayerSequence A π m n h hπ d V hV).f.hom =
      (boundaryPowerLayerSequence A π m n h hπ d U hU).f.hom.comp
        (closedLayerMap A π m f) := by
  let _ := boundaryPowerSections_flat A π (m + 1) n h d U hU
  let _ := boundaryPowerSections_flat A π (m + 1) n h d V hV
  exact closedLayerInclusion_natural A π hπ m _

end FLT.Mazur.PolygonArithmeticStages
