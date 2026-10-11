/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseOpenHilbertOrbitOpen
public import FLT.Mazur.BaseOpenHilbertRestrictedRelation

/-!
# Point fibers of a base-local Hilbert quotient chart

The actual chart parameter and actual orbit map have exactly the same point
fibers. Scheme pullbacks supply common extension points; no preservation of
fiber products by the underlying-point functor is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve RelativeRelationOrbit
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [IsOpenImmersion V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))

omit [IsOpenImmersion V.hom] in
/-- A relation between source-chart points lifts to the actual restricted relation scheme. -/
theorem baseOpenRestricted_point_lift (x y : (variableSourceIntersection f hL d V c).left)
    (a : (smoothHilbertRelation f hL).left)
    (ha : (smoothHilbertRelationFst f hL).left a = (variableSourceInclusion f hL d V c).left x)
    (hb : (smoothHilbertRelationSnd f hL).left a = (variableSourceInclusion f hL d V c).left y) :
    ∃ z : (baseOpenRestrictedRelation f hL d V c).left,
      (baseOpenRestrictedFst f hL d V c).left z = x ∧
        (baseOpenRestrictedSnd f hL d V c).left z = y := by
  have H₁ := (IsPullback.of_hasPullback
    (smoothHilbertRelationFst f hL) (variableSourceInclusion f hL d V c)).map (Over.forget _)
  obtain ⟨b, hb₁, hb₂⟩ := Scheme.exists_preimage_of_isPullback H₁ a x ha
  have he : (baseOpenRelationOther f hL d V c).left b =
      (variableSourceInclusion f hL d V c).left y := by
    exact (congrArg (smoothHilbertRelationSnd f hL).left hb₁).trans hb
  have H₂ := (IsPullback.of_hasPullback
    (baseOpenRelationOther f hL d V c) (variableSourceInclusion f hL d V c)).map (Over.forget _)
  obtain ⟨z, hz₁, hz₂⟩ := Scheme.exists_preimage_of_isPullback H₂ b y he
  refine ⟨z, ?_, hz₂⟩
  exact (congrArg (pullback.snd (smoothHilbertRelationFst f hL)
    (variableSourceInclusion f hL d V c)).left hz₁).trans hb₂

/-- The original orbit relation is exactly equality of actual chart parameters. -/
theorem baseOpenSource_related_iff (x y : (variableSourceIntersection f hL d V c).left) :
    Related (smoothHilbertRelationFst f hL) (smoothHilbertRelationSnd f hL)
      ((variableSourceInclusion f hL d V c).left x) ((variableSourceInclusion f hL d V c).left y) ↔
    (variableSourceParameter f hL d V c).left x = (variableSourceParameter f hL d V c).left y := by
  constructor
  · rintro ⟨a, ha, hb⟩
    obtain ⟨z, hx, hy⟩ := baseOpenRestricted_point_lift f hL d V c x y a ha hb
    have h := congrArg (fun k ↦ k.left z) (baseOpenRestricted_condition f hL d V c)
    change (variableSourceParameter f hL d V c).left ((baseOpenRestrictedFst f hL d V c).left z) =
      (variableSourceParameter f hL d V c).left ((baseOpenRestrictedSnd f hL d V c).left z) at h
    rwa [hx, hy] at h
  · intro h
    have H := (baseOpenRestricted_isPullback f hL d V c).map (Over.forget _)
    obtain ⟨z, hx, hy⟩ := Scheme.exists_preimage_of_isPullback H x y h
    refine ⟨(baseOpenRestrictedToRelation f hL d V c).left z, ?_, ?_⟩
    · exact (congrArg (fun k ↦ k.left z) (baseOpenRestrictedToRelation_fst f hL d V c)).trans
        (congrArg (variableSourceInclusion f hL d V c).left hx)
    · exact (congrArg (fun k ↦ k.left z) (baseOpenRestrictedToRelation_snd f hL d V c)).trans
        (congrArg (variableSourceInclusion f hL d V c).left hy)

/-- The two surjections from the source chart have precisely the same fibers. -/
theorem baseOpenSourceOrbitMap_eq_iff (x y : (variableSourceIntersection f hL d V c).left) :
    baseOpenSourceOrbitMap f hL d V c x = baseOpenSourceOrbitMap f hL d V c y ↔
      (variableSourceParameter f hL d V c).left x =
        (variableSourceParameter f hL d V c).left y := by
  rw [Subtype.ext_iff]
  exact (projection_eq_iff (smoothHilbertEquivalenceRelation f hL) _ _).trans
    (baseOpenSource_related_iff f hL d V c x y)

end FLT.Mazur.HilbertChart
