/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SmoothTranslationOrbitCover
public import FLT.Mazur.VariableHilbertParameterOrbitDescent

/-!
# The covering smooth parameters retain their original locally ringed maps

For the fixed ordered family, the parameter's descended orbit map is exactly
its original coproduct inclusion followed by the invariant quotient map.
Consequently its map to the original quotient carries the original structure
sheaf morphism, rather than only a continuous map.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Topology
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve RelativeRelationOrbit OrderedCurvePower
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (i : SmoothHilbertTranslationIndex)

/-- The ordered chart has a canonical lift into its common source intersection. -/
def orderedTranslationCommonLift : smoothHilbertTest f i ⟶
    variableSourceIntersection f hL i.2 (smoothTranslationTest f i.1)
      (smoothTranslationClass f hL.2.1 i.1) :=
  (variableHilbertOverlap_lift f i.2 hL (smoothTranslationTest f i.1)
    (smoothTranslationClass f hL.2.1 i.1) _ (smoothHilbertSourceSection f hL)
    (smoothHilbertSourceArrow f i) (𝟙 _) (by
      simpa only [Category.id_comp, smoothHilbertPoint] using
        (smoothHilbertSourceSection_chart f hL i (𝟙 _)).symm)).choose

/-- Its actual original source coordinate is the original coproduct inclusion. -/
theorem orderedTranslationCommonLift_source :
    orderedTranslationCommonLift f hL i ≫ variableSourceInclusion f hL i.2
      (smoothTranslationTest f i.1) (smoothTranslationClass f hL.2.1 i.1) =
        smoothHilbertSourceArrow f i :=
  (variableHilbertOverlap_lift f i.2 hL (smoothTranslationTest f i.1)
    (smoothTranslationClass f hL.2.1 i.1) _ (smoothHilbertSourceSection f hL)
    (smoothHilbertSourceArrow f i) (𝟙 _) (by
      simpa only [Category.id_comp, smoothHilbertPoint] using
        (smoothHilbertSourceSection_chart f hL i (𝟙 _)).symm)).choose_spec.1.1

/-- Its actual parameter coordinate is the identity. -/
theorem orderedTranslationCommonLift_parameter :
    orderedTranslationCommonLift f hL i ≫ variableSourceParameter f hL i.2
      (smoothTranslationTest f i.1) (smoothTranslationClass f hL.2.1 i.1) = 𝟙 _ :=
  (variableHilbertOverlap_lift f i.2 hL (smoothTranslationTest f i.1)
    (smoothTranslationClass f hL.2.1 i.1) _ (smoothHilbertSourceSection f hL)
    (smoothHilbertSourceArrow f i) (𝟙 _) (by
      simpa only [Category.id_comp, smoothHilbertPoint] using
        (smoothHilbertSourceSection_chart f hL i (𝟙 _)).symm)).choose_spec.1.2

/-- The covering parameter's actual locally ringed map to the original invariant quotient. -/
def orderedTranslationLocallyRingedMap : (smoothHilbertTest f i).left.toLocallyRingedSpace ⟶
    smoothHilbertInvariantQuotient f hL :=
  (smoothHilbertSourceArrow f i).left.toLRSHom ≫ smoothHilbertInvariantProjection f hL

/-- The descended topological chart map is the actual original locally ringed map. -/
theorem orderedTranslationLocallyRingedMap_apply (x : (smoothHilbertTest f i).left) :
    (orderedTranslationLocallyRingedMap f hL i).base x =
      (smoothTranslationChartToOrbit f hL i.2 (smoothTranslationTest f i.1)
        (smoothTranslationClass f hL.2.1 i.1) x).val := by
  have h := smoothTranslationChartToOrbit_parameter f hL i.2
    (smoothTranslationTest f i.1) (smoothTranslationClass f hL.2.1 i.1)
    ((orderedTranslationCommonLift f hL i).left x)
  have hp := congrArg (fun k ↦ k.left x) (orderedTranslationCommonLift_parameter f hL i)
  change (variableSourceParameter f hL i.2 _ _).left
    ((orderedTranslationCommonLift f hL i).left x) = x at hp
  rw [hp] at h
  have hs := congrArg (fun k ↦ k.left x) (orderedTranslationCommonLift_source f hL i)
  change (smoothHilbertInvariantProjection f hL).base
    ((smoothHilbertSourceArrow f i).left x) = _
  rw [smoothHilbertInvariantProjection_base]
  exact (congrArg (projection (smoothHilbertEquivalenceRelation f hL)) hs).symm.trans
    (congrArg Subtype.val h).symm

/-- The actual locally ringed map has exactly the constructed covering neighborhood as image. -/
theorem orderedTranslationLocallyRingedMap_range :
    Set.range (orderedTranslationLocallyRingedMap f hL i).base =
      (orderedTranslationOrbitOpen f hL i).carrier := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    rw [orderedTranslationLocallyRingedMap_apply]
    exact (smoothTranslationChartToOrbit f hL i.2 _ _ x).property
  · intro hz
    obtain ⟨x, hx⟩ := smoothTranslationChartToOrbit_surjective f hL i.2
      (smoothTranslationTest f i.1) (smoothTranslationClass f hL.2.1 i.1) ⟨z, hz⟩
    exact ⟨x, (orderedTranslationLocallyRingedMap_apply f hL i x).trans
      (congrArg Subtype.val hx)⟩

/-- All points are covered by the actual locally ringed maps from the ordered parameters. -/
theorem orderedTranslationLocallyRingedMap_covers
    (z : smoothHilbertInvariantQuotient f hL) :
    ∃ i, z ∈ Set.range (orderedTranslationLocallyRingedMap f hL i).base := by
  obtain ⟨i, hi⟩ := orderedTranslationOrbitOpen_covers f hL z
  exact ⟨i, (Set.ext_iff.mp (orderedTranslationLocallyRingedMap_range f hL i) z).mpr hi⟩

end FLT.Mazur.HilbertChart
