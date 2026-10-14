/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteSmoothFieldCyclic
public import FLT.Mazur.PolygonCompleteCyclicSchemeAction
public import FLT.Mazur.PolygonProjectiveTranslation

/-!
# Original smooth field rotations are translations in the full group

The cubic translation equality transports back to the original whole curve.
The translating point is exactly the original unshifted cyclic section.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj CartesianMonoidalCategory
namespace FLT.Mazur.PolygonInfinitesimalStages
open WeierstrassIntegralChart GroupObjectPointTranslation PolygonPinching
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completeProjectiveRotationIso translation
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  (L : Type) [Field L] (a : PowerSeries K →+* L) (ha : a PowerSeries.X ≠ 0)
  {Y : Scheme} (p : Y ⟶ exactVeroneseProj K n h) (q : Y ⟶ Spec (.of L))
  (hs : IsPullback p q (exactVeroneseProjToBase K n h)
    (Spec.map (CommRingCat.ofHom a)))
local notation "s" => Spec.map (CommRingCat.ofHom a)
local notation "e" => completeFieldCubicOverIso K n h L a ha p q hs (0 : Fin n)
local notation "cg" => completeFieldCubicCommGrp K n h L a ha p q hs (0 : Fin n)
local notation "fg" => completeFieldCommGrp K n h L a ha p q hs (0 : Fin n)

/-- The original identity rotates to precisely the original cyclic section. -/
theorem completeFieldRotation_identity (b : ZMod n) :
    let _ := fg
    (1 : 𝟙_ (Over (Spec (.of L))) ⟶ Over.mk q) ≫
      completeCartesianRotationOver K n h s p q hs b =
        completeCyclicSection K n h s p q hs b := by
  let _ := fg
  apply Over.OverMorphism.ext
  change (η[Over.mk q]).left ≫ completeCartesianRotation K n h s p q hs b = _
  rw [completeFieldCommGrp_identity, completeCartesianMarking_rotation]
  simp only [completeCyclicSection, Over.homMk_left, rotateIndex, map_zero, zero_add]

/-- The whole original field rotation equals translation in the constructed full group. -/
theorem completeFieldRotation_eq_translation (b : ZMod n) :
    let _ := fg
    completeCartesianRotationOver K n h s p q hs b =
      translation (completeCyclicSection K n h s p q hs b) := by
  let _ := cg
  let _ := fg
  let _ : IsMonHom (e).inv := isMonHom_ofIso (e).symm
  let _ : IsMonHom (e).hom := inferInstanceAs (IsMonHom (e).symm.inv)
  let W := completeCartesianPointWeierstrass K n h L s p q hs (0 : Fin n)
  let r := curveAutomorphismOverIso W
    (completeProjectiveRotationIso K n h L a ha p q hs (0 : Fin n) b)
    (completeProjectiveRotationIso_over K n h L a ha p q hs (0 : Fin n) b)
  have hr : (e).hom ≫ r.hom = completeCartesianRotationOver K n h s p q hs b ≫ (e).hom := by
    apply Over.OverMorphism.ext
    exact completePointProjectiveIso_rotation K n h L a ha p q hs (0 : Fin n) b
  have hp : (1 : 𝟙_ (Over (Spec (.of L))) ⟶ integralCurveOver W) ≫ r.hom =
      completeCyclicSection K n h s p q hs b ≫ (e).hom := by
    rw [← MonObj.one_comp (e).hom, Category.assoc, hr, ← Category.assoc,
      completeFieldRotation_identity]
  apply (cancel_mono (e).hom).mp
  rw [← hr, completeProjectiveRotation_eq_translation, comp_translation, hp]
  simp only [translation, MonObj.mul_comp, Category.assoc, Category.id_comp]

/-- The original rotation law holds on sections of every test scheme over the field. -/
theorem completeFieldRotation_test (b : ZMod n) {T : Over (Spec (.of L))}
    (x : T ⟶ Over.mk q) :
    let _ := fg
    x ≫ completeCartesianRotationOver K n h s p q hs b =
      (toUnit T ≫ completeCyclicSection K n h s p q hs b) * x := by
  let _ := fg
  rw [completeFieldRotation_eq_translation, comp_translation]

end FLT.Mazur.PolygonInfinitesimalStages
