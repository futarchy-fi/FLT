/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SmoothCurveCommonOpenIso
public import Mathlib.AlgebraicGeometry.Geometrically.Integral

/-!
# Field base change of a relative common-open comparison

The map compared here is the base change of the given original morphism.
Nonemptiness of the common open on the field test supplies density on both
integral fibers, where the smooth-curve extension theorem applies.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.FCurve

set_option backward.isDefEq.respectTransparency false
universe u

/-- A relative common open identifies the actual original morphism on every field test. -/
theorem smoothCurve_commonOpen_fieldBaseChange_isIso
    {S X Y U : Scheme.{u}} (q : X ⟶ S) (r : Y ⟶ S)
    [IsProper q] [IsSeparated r] [SmoothOfRelativeDimension 1 r]
    [GeometricallyIntegral q] [GeometricallyIntegral r]
    (j : U ⟶ X) [IsOpenImmersion j] (k : U ⟶ Y) [IsOpenImmersion k]
    (f : X ⟶ Y) (hf : f ≫ r = q) (hjk : j ≫ f = k)
    {K : Type u} [Field K] (b : Spec (.of K) ⟶ S)
    [Nonempty (pullback (k ≫ r) b : Scheme.{u})] :
    IsIso (pullback.map q b r b f (𝟙 _) (𝟙 _) (by simpa using hf.symm) (by simp)) := by
  let a : pullback (k ≫ r) b ⟶ pullback q b :=
    pullback.map _ _ _ _ j (𝟙 _) (𝟙 _)
      (by simp only [← hjk, Category.assoc, Category.comp_id, hf])
      (by simp)
  let c : pullback (k ≫ r) b ⟶ pullback r b :=
    pullback.map _ _ _ _ k (𝟙 _) (𝟙 _) (by simp) (by simp)
  let g : pullback q b ⟶ pullback r b :=
    pullback.map _ _ _ _ f (𝟙 _) (𝟙 _) (by simpa using hf.symm) (by simp)
  let _ : IsOpenImmersion a := by dsimp [a]; infer_instance
  let _ : IsOpenImmersion c := by dsimp [c]; infer_instance
  let _ : IsIntegral (pullback q b) :=
    GeometricallyIntegral.geometrically_isIntegral b _ _ (.of_hasPullback _ _)
  let _ : IsIntegral (pullback r b) :=
    GeometricallyIntegral.geometrically_isIntegral b _ _ (.of_hasPullback _ _)
  let _ : SmoothOfRelativeDimension 1 (pullback.snd r b) :=
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) r b inferInstance
  apply smoothCurve_isIso_of_commonOpen (pullback.snd q b) (pullback.snd r b) a c g
  · simp [g]
  · apply pullback.hom_ext <;> simp [a, c, g, hjk]

end FLT.Mazur.FCurve
