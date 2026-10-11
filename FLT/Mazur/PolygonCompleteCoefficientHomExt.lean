/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteLineSectionReconstruction
public import FLT.Mazur.PolygonCompleteBoundaryCoordinateTransport

/-!
# Original stages detect complete coefficient-line morphisms

The actual coefficient sections generate the complete coefficient line.
Formal section uniqueness for the target therefore proves that all original
stage restrictions jointly detect a morphism, including a proposed marked-line comparison.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules

namespace FLT.Mazur.PolygonInfinitesimalStages

open FCurve ModuleLineBundleTensorPullback

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] completeCoefficientCoordinates
  originalStageToCompatibleProj ModuleSheafTensor.tensor

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- The original complete coefficient sections determine morphisms into any module. -/
theorem completeCoefficientHom_ext_coordinates
    {M : (exactVeroneseProj K n h).Modules} (a b : completeCoefficientLine K n h ⟶ M)
    (hs : ∀ i, a.app ⊤ (completeCoefficientSection K n h i) =
      b.app ⊤ (completeCoefficientSection K n h i)) : a = b :=
  GradedProjLine.coefficientSection_hom_ext _ _
    (completeCoefficientCoordinates K n h).homogeneous
    (completeCoefficientCoordinates K n h).covers a b hs

/-- Original finite-stage pullbacks jointly detect maps from the coefficient line to a line. -/
theorem completeCoefficientHom_ext_stages
    {M : (exactVeroneseProj K n h).Modules} (hM : LocallyFreeRankOne M)
    (a b : completeCoefficientLine K n h ⟶ M)
    (hs : ∀ m, (pullback (originalStageToCompatibleProj K n h m)).map a =
      (pullback (originalStageToCompatibleProj K n h m)).map b) : a = b := by
  apply completeCoefficientHom_ext_coordinates K n h a b
  intro i
  apply completeLineSection_ext K n h M hM
  intro m
  rw [← pullGlobal_naturality, ← pullGlobal_naturality, hs m]

/-- A complete coefficient-line isomorphism is unique once its original stages are fixed. -/
theorem completeCoefficientIso_ext_stages
    {M : (exactVeroneseProj K n h).Modules} (hM : LocallyFreeRankOne M)
    (a b : completeCoefficientLine K n h ≅ M)
    (hs : ∀ m, (pullback (originalStageToCompatibleProj K n h m)).mapIso a =
      (pullback (originalStageToCompatibleProj K n h m)).mapIso b) : a = b := by
  apply Iso.ext
  exact completeCoefficientHom_ext_stages K n h hM a.hom b.hom
    (fun m ↦ congrArg Iso.hom (hs m))

end FLT.Mazur.PolygonInfinitesimalStages
