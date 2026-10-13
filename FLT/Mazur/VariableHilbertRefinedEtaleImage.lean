/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.VariableHilbertDescendedGeometry
public import FLT.Mazur.VariableHilbertEffectiveEtaleImage
public import FLT.Mazur.VariableHilbertRefinedPicardImage

/-!
# Arbitrary fppf refined models retain the original etale image

The original projection is now an effective fppf model in its own right.
Its descended section agrees exactly with the refined section. For an etale
original translation base this identifies the represented image with the
original etale-local image, without an etaleness hypothesis on the refinement.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.VariableHilbertFppfRefinement
open HilbertChart CartierAbel SchemePicard FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) {V W : Over (Spec (.of R))} (b : W ⟶ V)
  (c : (relativeFppfSheaf f).obj.obj (op V))
  [Flat b.left] [LocallyOfFinitePresentation b.left] [Surjective b.left]
  {Z : Over (Spec (.of R))} (π : variableHilbertTest f d W ⟶ Z)
  (H : IsPullback
    (variableChartRelationFst f hL d W ((relativeFppfSheaf f).obj.map b.op c))
    (variableChartRelationSnd f hL d W ((relativeFppfSheaf f).obj.map b.op c)) π π)
  [Flat π.left] [LocallyOfFinitePresentation π.left] [Surjective π.left]
local notation "cW" => CategoryTheory.Functor.map
  (ObjectProperty.FullSubcategory.obj (relativeFppfSheaf f)) (Quiver.Hom.op b) c
local notation "D" => descendedProjection f hL d b c π H.w
local notation "HD" => descendedProjection_isPullback f hL d b c π H
local notation "sZ" => effectivePicardSection f hL d W cW π H
local notation "s" => variableChartSection f hL d V c

/-- The original effective section is independent of the arbitrary fppf refinement. -/
theorem descendedEffectivePicardSection_eq [LocallyOfFinitePresentation V.hom] :
    let _ := descendedProjection_locallyOfFinitePresentation f hL d b c π H
    effectivePicardSection f hL d V c D HD = sZ := by
  let _ := descendedProjection_locallyOfFinitePresentation f hL d b c π H
  exact (effectivePicardSection_unique f hL d V c D HD sZ
    (descendedProjection_picard f hL d b c π H)).symm

/-- Every represented original section has an etale-local ORIGINAL parameter representative. -/
theorem descendedPicardEtaleImage_iff [Etale V.hom] {T : Over (Spec (.of R))}
    (z : (relativeFppfSheaf f).obj.obj (op T)) :
    (∃ k : T ⟶ Z, (relativeFppfSheaf f).obj.map k.op sZ = z) ↔
      ∃ (T' : Over (Spec (.of R))) (t : T' ⟶ T)
        (a : T' ⟶ variableHilbertTest f d V),
        Etale t.left ∧ Surjective t.left ∧
          (relativeFppfSheaf f).obj.map t.op z = (relativeFppfSheaf f).obj.map a.op s := by
  let _ := descendedProjection_locallyOfFinitePresentation f hL d b c π H
  rw [← descendedEffectivePicardSection_eq f hL d b c π H]
  exact effectivePicardEtaleImage_iff f hL d V c D HD z

/-- Original etale-local representatives determine a unique map into the refined model. -/
theorem descendedPicardEtaleImage_existsUnique [Etale V.hom]
    {T T' : Over (Spec (.of R))} (t : T' ⟶ T) [Etale t.left] [Surjective t.left]
    (a : T' ⟶ variableHilbertTest f d V) (z : (relativeFppfSheaf f).obj.obj (op T))
    (hz : (relativeFppfSheaf f).obj.map t.op z = (relativeFppfSheaf f).obj.map a.op s) :
    ∃! k : T ⟶ Z, (relativeFppfSheaf f).obj.map k.op sZ = z := by
  obtain ⟨k, hk⟩ := (descendedPicardEtaleImage_iff f hL d b c π H z).mpr
    ⟨T', t, a, inferInstance, inferInstance, hz⟩
  exact ⟨k, hk, fun l hl ↦
    effectivePicardSection_injective f hL d W cW π H T (hl.trans hk.symm)⟩

end FLT.Mazur.VariableHilbertFppfRefinement
