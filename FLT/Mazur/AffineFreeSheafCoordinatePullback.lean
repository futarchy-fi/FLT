/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineFreeSheafCoordinateNormalization

/-!
# Coefficient squares for recovered affine free coordinates

Actual sheaf pullback squares yield coefficient squares for the recovered
linear equivalences. This applies in particular to canonical free pullback.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.AffineFreeSheafCoordinates
open AffineModuleGlobalSections FreeSheafSectionCoordinates FCurve ProjectiveSpace
variable {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y)
attribute [local irreducible] sectionIso coordinatesIso

/-- An actual pullback square induces the concrete semilinear coordinate square. -/
lemma coordinates_coefficient_square {ι κ : Type u}
    (e : (SheafOfModules.free ι : Y.Modules) ≅ SheafOfModules.free κ)
    (d : (SheafOfModules.free ι : X.Modules) ≅ SheafOfModules.free κ)
    (h : (pullback f).map e.hom ≫ (ModuleGlobalEvaluationPullback.freeIso f κ).hom =
      (ModuleGlobalEvaluationPullback.freeIso f ι).hom ≫ d.hom)
    (v : ι →₀ Γ(Y, ⊤)) :
    changeCoefficients f.appTop.hom (coordinates Y e v) =
      coordinates X d (changeCoefficients f.appTop.hom v) := by
  apply realize_injective X κ
  rw [← realize_pullback, realize_coordinates, realize_coordinates, ← realize_pullback]
  change (ModuleGlobalEvaluationPullback.freeIso f κ).hom.app ⊤
    (pullGlobal f _ (Hom.app e.hom ⊤ (realize Y ι v))) = _
  rw [← pullGlobal_naturality]
  exact congrArg (fun k ↦ k.app ⊤ (pullGlobal f _ (realize Y ι v))) h

/-- The coordinate change obtained by pulling back an actual free sheaf isomorphism. -/
def pullbackFreeIso {ι κ : Type u}
    (e : (SheafOfModules.free ι : Y.Modules) ≅ SheafOfModules.free κ) :
    (SheafOfModules.free ι : X.Modules) ≅ SheafOfModules.free κ :=
  (ModuleGlobalEvaluationPullback.freeIso f ι).symm ≪≫
    (pullback f).mapIso e ≪≫ ModuleGlobalEvaluationPullback.freeIso f κ

/-- Recovered coordinates commute with arbitrary affine pullback. -/
lemma coordinates_pullback {ι κ : Type u}
    (e : (SheafOfModules.free ι : Y.Modules) ≅ SheafOfModules.free κ)
    (v : ι →₀ Γ(Y, ⊤)) :
    changeCoefficients f.appTop.hom (coordinates Y e v) =
      coordinates X (pullbackFreeIso f e) (changeCoefficients f.appTop.hom v) := by
  apply coordinates_coefficient_square
  simp [pullbackFreeIso]

/-- Actual projective coordinate changes commute with the coefficient morphism. -/
lemma linearIso_coordinates_pullback {ι κ : Type u}
    (e : (SheafOfModules.free ι : Y.Modules) ≅ SheafOfModules.free κ) :
    coefficientMap f.appTop.hom ι ≫ (linearIso (coordinates Y e)).hom =
      (linearIso (coordinates X (pullbackFreeIso f e))).hom ≫
        coefficientMap f.appTop.hom κ :=
  linearIso_coefficientMap _ _ _ (coordinates_pullback f e)

end FLT.Mazur.AffineFreeSheafCoordinates
