/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonPinchingFlatBaseChange
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# The normalization inclusion of structure sheaves

The canonical map of actual module sheaves is injective on every open: finite
surjective normalization is schematically dominant because the polygon is reduced.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
@[expose] public noncomputable section
universe u
namespace FLT.Mazur.PolygonStructureInclusion
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open Scheme.Modules PolygonPinching
variable (K : Type u) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
variable {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
/-- The actual structure sheaf as a sheaf of modules. -/
abbrev structureModule (X : Scheme.{u}) : X.Modules := SheafOfModules.unit X.ringCatSheaf
/-- The direct image of the normalization's structure sheaf. -/
abbrev normalizationModule : C.left.Modules :=
  (pushforward p.left).obj (structureModule (components K n).left)
/-- The canonical map from the polygon structure sheaf to its normalization's direct image. -/
def inclusion : structureModule C.left ⟶ normalizationModule K n p :=
  SheafOfModules.unitToPushforwardObjUnit p.left.toRingCatSheafHom
omit [NeZero n] in
@[simp] theorem inclusion_app (U : C.left.Opens) (r : Γ(C.left, U)) :
    (inclusion K n p).val.app (.op U) r = p.left.app U r := rfl
include h in
theorem normalization_dominant : IsSchemeTheoreticallyDominant p.left := by
  have : IsIso (polygonIso K n hn p q h).hom.left :=
    inferInstanceAs (IsIso ((Over.forget _).map (polygonIso K n hn p q h).hom))
  rw [← normalization_polygonIso K n hn p q h]
  change IsSchemeTheoreticallyDominant ((PolygonAtlas.normalization K n).left ≫ _)
  infer_instance
include h in
theorem inclusion_injective (U : C.left.Opens) :
    Function.Injective ((inclusion K n p).val.app (.op U)) := by
  let := normalization_dominant K n hn p q h
  let := PolygonNormalizationFinite.cocone_normalization_finite K n hn p q h
  exact p.left.app_injective U
include h in
theorem inclusion_mono : Mono (inclusion K n p) := by
  constructor
  intro M a b hab
  ext U x
  apply inclusion_injective K n hn p q h U
  exact congrArg (fun f ↦ f.val.app (.op U) x) hab
end FLT.Mazur.PolygonStructureInclusion
