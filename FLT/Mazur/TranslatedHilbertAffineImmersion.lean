/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.TranslatedHilbertLocallyRingedChart

/-!
# Affine open immersions into the actual translated orbit quotient

The original parameter opens map by locally ringed open immersions into the
invariant quotient. Their images are exactly the previously constructed
transported opens. Affine parameter opens therefore give actual affine charts.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve RelativeRelationOrbit
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (i : TranslatedHilbertIndex f)

/-- A parameter open maps into the original invariant quotient as a locally ringed space. -/
def translatedParameterOpenImmersion (W : (acyclicHilbertTest f i.1).left.Opens) :
    W.toScheme.toLocallyRingedSpace ⟶
      invariantLocallyRingedSpace (smoothHilbertEquivalenceRelation f hL) :=
  W.ι.toLRSHom ≫ (translatedOrbitChartLocallyRingedIso f hL i).inv ≫
    (invariantLocallyRingedSpace (smoothHilbertEquivalenceRelation f hL)).ofRestrict
      (Opens.isOpenEmbedding (X := space (smoothHilbertEquivalenceRelation f hL))
        (translatedOrbitOpen f hL i))

instance translatedParameterOpenImmersion_isOpenImmersion
    (W : (acyclicHilbertTest f i.1).left.Opens) :
    LocallyRingedSpace.IsOpenImmersion (translatedParameterOpenImmersion f hL i W) := by
  delta translatedParameterOpenImmersion
  infer_instance

/-- The immersion retains the original parameter-to-orbit function. -/
theorem translatedParameterOpenImmersion_apply
    (W : (acyclicHilbertTest f i.1).left.Opens) (x : W) :
    (translatedParameterOpenImmersion f hL i W).base x =
      (translatedChartToOrbit f hL i x.val).val := rfl

/-- Its actual image is the transported open of the original orbit space. -/
theorem translatedParameterOpenImmersion_range
    (W : (acyclicHilbertTest f i.1).left.Opens) :
    Set.range (translatedParameterOpenImmersion f hL i W).base =
      ((translatedChartOrbitOpens f hL i).obj W).carrier := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨translatedChartToOrbit f hL i x.val, ?_, rfl⟩
    change translatedOrbitToChart f hL i (translatedChartToOrbit f hL i x.val) ∈ W
    exact ((translatedOrbitChartHomeomorph f hL i).apply_symm_apply x.val).symm ▸ x.property
  · rintro ⟨x, hx, rfl⟩
    refine ⟨⟨translatedOrbitToChart f hL i x, hx⟩, ?_⟩
    change (translatedChartToOrbit f hL i (translatedOrbitToChart f hL i x)).val = x.val
    exact congrArg Subtype.val ((translatedOrbitChartHomeomorph f hL i).symm_apply_apply x)

/-- Every point of this chart lies in the image of an affine parameter open. -/
theorem translatedOrbitOpen_exists_affine (z : translatedOrbitOpen f hL i) :
    ∃ W : (acyclicHilbertTest f i.1).left.Opens, IsAffineOpen W ∧
      z.val ∈ Set.range (translatedParameterOpenImmersion f hL i W).base := by
  obtain ⟨W, hW, hz, _⟩ := exists_isAffineOpen_mem_and_subset
    (X := (acyclicHilbertTest f i.1).left)
    (x := translatedOrbitToChart f hL i z) (U := ⊤) trivial
  refine ⟨W, hW, ⟨⟨translatedOrbitToChart f hL i z, hz⟩, ?_⟩⟩
  change (translatedChartToOrbit f hL i (translatedOrbitToChart f hL i z)).val = z.val
  exact congrArg Subtype.val ((translatedOrbitChartHomeomorph f hL i).symm_apply_apply z)

end FLT.Mazur.HilbertChart
