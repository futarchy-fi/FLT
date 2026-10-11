/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PointNormalizedDirectImage
public import FLT.Mazur.ClosedPointLineSection
public import FLT.Mazur.ProperLineCoefficientFiberComparison

/-!
# Fiber cohomology is invariant under point normalization

A base line becomes trivial over each residue field. Tensor pullback and
that actual trivialization identify the entire original fiber sheaves, so
cohomology vanishing in every degree is preserved and detected.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.FCurve
open ModuleSheafTensor ModuleSheafTensorCurrying
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] tensor
variable {X S : Scheme.{0}} (f : X ⟶ S) (L : X.Modules)
  {B : S.Modules} (hB : LocallyFreeRankOne B)

include hB in
/-- A base-line twist is isomorphic to the original sheaf on every actual residue fiber. -/
theorem baseLineTwist_fiber_iso (s : S) :
    Nonempty ((pullback (f.fiberι s)).obj (tensor L ((pullback f).obj B)) ≅
      (pullback (f.fiberι s)).obj L) := by
  let b := S.fromSpecResidueField s
  let q := f.fiberToSpecResidueField s
  obtain ⟨e⟩ := (hB.pullback b).trivial_of_subsingleton (Classical.arbitrary _)
  let d : (pullback (f.fiberι s)).obj ((pullback f).obj B) ≅
      structureModule (f.fiber s) :=
    (pullbackComp (f.fiberι s) f).app B ≪≫
      (pullbackCongr Limits.pullback.condition).app B ≪≫
      ((pullbackComp q b).app B).symm ≪≫
      (pullback q).mapIso e ≪≫ modulePullbackUnitIso q
  exact ⟨ModuleLineBundleTensorPullback.tensorIso (f.fiberι s) L _ ≪≫
    congr (Iso.refl _) d ≪≫ rightUnitor _⟩

include hB in
/-- Every degree of fiber cohomology detects vanishing before or after a base-line twist. -/
theorem baseLineTwist_fiber_vanishing_iff (s : S) (n : ℕ) :
    Subsingleton (ModuleH ((pullback (f.fiberι s)).obj
      (tensor L ((pullback f).obj B))) n) ↔
      Subsingleton (ModuleH ((pullback (f.fiberι s)).obj L) n) := by
  obtain ⟨e⟩ := baseLineTwist_fiber_iso f L hB s
  exact Equiv.subsingleton_congr (moduleHIsoOfIso e n).toEquiv

end FLT.Mazur.FCurve

namespace FLT.Mazur.SchemePicard
open FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] ModuleSheafTensor.tensor
variable {X S : Scheme.{0}} (f : X ⟶ S) (e : S ⟶ X)
  (L : X.Modules) (hL : LocallyFreeRankOne L)

include hL in
/-- Actual point normalization preserves and detects fiber cohomology vanishing in every degree. -/
theorem pointNormalizedLine_fiber_vanishing_iff (s : S) (n : ℕ) :
    Subsingleton (ModuleH ((Scheme.Modules.pullback (f.fiberι s)).obj
      (pointNormalizedLine f e L)) n) ↔
      Subsingleton (ModuleH ((Scheme.Modules.pullback (f.fiberι s)).obj L) n) := by
  unfold pointNormalizedLine
  exact baseLineTwist_fiber_vanishing_iff f L (hL.pullback e).dual s n

end FLT.Mazur.SchemePicard
