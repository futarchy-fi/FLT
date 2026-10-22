/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperCurveOpenComparison
public import FLT.Mazur.SchemeUnchangedOpen
public import Mathlib.AlgebraicGeometry.Geometrically.Integral

/-!
# Singular curve comparisons after a field test

An actual Cartesian common open stays Cartesian under coefficient base change.
Equality of structure Euler characteristics recovers the whole original map
on the field test, including singular points, without a smoothness hypothesis.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.FCurve
set_option backward.isDefEq.respectTransparency false

/-- A Cartesian common open and equal Euler characteristics identify the field comparison. -/
theorem commonOpen_euler_fieldBaseChange_isIso
    {S X Y U : Scheme} (q : X ⟶ S) (r : Y ⟶ S)
    [IsProper q] [IsProper r] [GeometricallyIntegral q] [GeometricallyIntegral r]
    (j : U ⟶ X) (k : U ⟶ Y) [IsOpenImmersion k]
    (f : X ⟶ Y) (hf : f ≫ r = q) (H : IsPullback (𝟙 U) j k f)
    {K : Type} [Field K] (b : Spec (.of K) ⟶ S)
    [Nonempty (pullback (k ≫ r) b : Scheme)]
    (hd : topologicalKrullDim (pullback q b : Scheme) = 1)
    (he : curveEulerCharacteristic (pullback.snd q b)
      (structureModule (pullback q b)) =
      curveEulerCharacteristic (pullback.snd r b) (structureModule (pullback r b))) :
    IsIso (pullback.map q b r b f (𝟙 _) (𝟙 _)
      (by simpa using hf.symm) (by simp)) := by
  have hjk : j ≫ f = k := by simpa using H.w.symm
  let a : pullback (k ≫ r) b ⟶ pullback q b :=
    pullback.map _ _ _ _ j (𝟙 _) (𝟙 _)
      (by simp only [← hjk, Category.assoc, Category.comp_id, hf]) (by simp)
  let c : pullback (k ≫ r) b ⟶ pullback r b :=
    pullback.map _ _ _ _ k (𝟙 _) (𝟙 _) (by simp) (by simp)
  let g : pullback q b ⟶ pullback r b :=
    pullback.map _ _ _ _ f (𝟙 _) (𝟙 _) (by simpa using hf.symm) (by simp)
  have ha : IsPullback (pullback.fst (k ≫ r) b) a j (pullback.fst q b) := by
    apply IsPullback.of_bot (h₃₁ := b) _ (by simp [a]) (.of_hasPullback q b)
    simpa [a, ← hf, ← Category.assoc, hjk] using (IsPullback.of_hasPullback (k ≫ r) b)
  have hc : IsPullback (pullback.fst (k ≫ r) b) c k (pullback.fst r b) := by
    apply IsPullback.of_bot (h₃₁ := b) _ (by simp [c]) (.of_hasPullback r b)
    simpa [c] using (IsPullback.of_hasPullback (k ≫ r) b)
  have hg : g ≫ pullback.fst r b = pullback.fst q b ≫ f := by simp [g]
  have H' : IsPullback (𝟙 _) a c g := by
    apply IsPullback.of_right _ _ hc
    · simpa only [Category.comp_id, Category.id_comp, hg] using ha.paste_horiz H
    · apply pullback.hom_ext <;> simp [a, c, g, hjk]
  let _ : IsOpenImmersion c := by dsimp [c]; infer_instance
  let _ : IsIntegral (pullback q b) :=
    GeometricallyIntegral.geometrically_isIntegral b _ _ (.of_hasPullback _ _)
  let _ : IsIntegral (pullback r b) :=
    GeometricallyIntegral.geometrically_isIntegral b _ _ (.of_hasPullback _ _)
  let _ := SchemeUnchangedOpen.isIso_of_identity_pullback g c a H'
  have hgr : g ≫ pullback.snd r b = pullback.snd q b := by simp [g]
  let _ : IsProper (g ≫ pullback.snd r b) := by rw [hgr]; infer_instance
  apply properCurve_isIso_of_open_euler_eq g c.opensRange (pullback.snd r b) hd
  · exact Set.range_nonempty c
  · rw [hgr]
    exact he

end FLT.Mazur.FCurve
