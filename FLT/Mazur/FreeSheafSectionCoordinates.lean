/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FreeSheafRestrictionCoherence
public import FLT.Mazur.ProjectiveLinearCoefficientChange

/-!
# Finite-support coordinates as actual free sheaf sections

The canonical free generators realize coefficient vectors as global sections.
This realization commutes with arbitrary scheme pullback and coefficient change.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.FreeSheafSectionCoordinates
open FCurve ModuleGlobalEvaluationPullback ProjectiveSpace

/-- Realize a finite-support coefficient vector using the actual free sheaf generators. -/
def realize (X : Scheme.{u}) (ι : Type u) :
    (ι →₀ Γ(X, ⊤)) →ₗ[Γ(X, ⊤)] Γ((SheafOfModules.free ι : X.Modules), ⊤) :=
  Finsupp.linearCombination Γ(X, ⊤)
    (fun i ↦ (show structureModule X ⟶ SheafOfModules.free ι from
        SheafOfModules.ιFree i).app ⊤ (1 : Γ(X, ⊤)))

@[simp]
lemma realize_single (X : Scheme.{u}) {ι : Type u} (i : ι) (r : Γ(X, ⊤)) :
    realize X ι (Finsupp.single i r) =
      r • (show structureModule X ⟶ SheafOfModules.free ι from
        SheafOfModules.ιFree i).app ⊤ (1 : Γ(X, ⊤)) := by
  simp [realize]

/-- Pullback identifies each actual free generator with the corresponding new generator. -/
lemma pull_generator {X Y : Scheme.{u}} (f : X ⟶ Y) {ι : Type u} (i : ι) :
    (freeIso f ι).hom.app ⊤
      (pullGlobal f _ ((show structureModule Y ⟶ SheafOfModules.free ι from
        SheafOfModules.ιFree i).app ⊤ (1 : Γ(Y, ⊤)))) =
        (show structureModule X ⟶ SheafOfModules.free ι from
        SheafOfModules.ιFree i).app ⊤ (1 : Γ(X, ⊤)) := by
  rw [pullGlobal_hom]
  change (((pullback f).map (SheafOfModules.ιFree i)) ≫
    (freeIso f ι).hom).app ⊤ _ = _
  rw [freeIso_generator]
  change (show structureModule X ⟶ SheafOfModules.free ι from
    SheafOfModules.ιFree i).app ⊤
    (((modulePullbackUnitIso f).inv ≫ (modulePullbackUnitIso f).hom).app ⊤ (1 : Γ(X, ⊤))) = _
  simp

/-- Realization commutes with coefficient change along any scheme morphism. -/
lemma realize_pullback {X Y : Scheme.{u}} (f : X ⟶ Y) {ι : Type u}
    (v : ι →₀ Γ(Y, ⊤)) :
    (freeIso f ι).hom.app ⊤ (pullGlobal f _ (realize Y ι v)) =
      realize X ι (changeCoefficients f.appTop.hom v) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp [hv, hw]
  | single i r =>
    rw [realize_single, map_smulₛₗ, Hom.app_smul, pull_generator,
      changeCoefficients_single, realize_single]

end FLT.Mazur.FreeSheafSectionCoordinates
