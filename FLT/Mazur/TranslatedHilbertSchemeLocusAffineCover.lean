/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.TranslatedHilbertSchemeLocus

/-!
# An explicit affine open cover of the actual translated scheme locus

The affine parameter opens immerse in the constructed scheme locus, retaining
their original maps into the invariant quotient. Their images cover the locus
and provide an actual scheme open cover for subsequent descent arguments.
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

/-- The original image of every parameter open lies in the actual scheme locus. -/
theorem translatedParameterOpenImmersion_range_subset_locus
    (i : TranslatedHilbertIndex f) (W : (acyclicHilbertTest f i.1).left.Opens) :
    Set.range (translatedParameterOpenImmersion f hL i W).base ⊆
      Set.range (translatedSchemeLocusInclusion f hL).base := by
  rintro z ⟨x, rfl⟩
  change ∃ y : translatedSchemeLocusOpen f hL,
    y.val = (translatedParameterOpenImmersion f hL i W).base x
  refine ⟨⟨_, ?_⟩, rfl⟩
  apply (mem_translatedSchemeLocusOpen f hL _).mpr
  exact ⟨i, (translatedChartToOrbit f hL i x.val).property⟩

/-- Every parameter open maps into the original invariant scheme locus. -/
def translatedParameterToSchemeLocus (i : TranslatedHilbertIndex f)
    (W : (acyclicHilbertTest f i.1).left.Opens) : W.toScheme ⟶ translatedSchemeLocus f hL :=
  ⟨LocallyRingedSpace.IsOpenImmersion.lift (translatedSchemeLocusInclusion f hL)
    (translatedParameterOpenImmersion f hL i W)
    (translatedParameterOpenImmersion_range_subset_locus f hL i W)⟩

/-- The factored scheme morphism retains the actual quotient immersion. -/
theorem translatedParameterToSchemeLocus_comp (i : TranslatedHilbertIndex f)
    (W : (acyclicHilbertTest f i.1).left.Opens) :
    (translatedParameterToSchemeLocus f hL i W).toLRSHom ≫
      translatedSchemeLocusInclusion f hL = translatedParameterOpenImmersion f hL i W :=
  LocallyRingedSpace.IsOpenImmersion.lift_fac _ _
    (translatedParameterOpenImmersion_range_subset_locus f hL i W)

instance translatedParameterToSchemeLocus_isOpenImmersion (i : TranslatedHilbertIndex f)
    (W : (acyclicHilbertTest f i.1).left.Opens) :
    IsOpenImmersion (translatedParameterToSchemeLocus f hL i W) := by
  change LocallyRingedSpace.IsOpenImmersion _
  unfold translatedParameterToSchemeLocus LocallyRingedSpace.IsOpenImmersion.lift
  infer_instance

/-- The explicit affine charts retain their actual affine scheme domains. -/
abbrev TranslatedLocusAffineIndex :=
  Σ i : TranslatedHilbertIndex f, (acyclicHilbertTest f i.1).left.affineOpens

/-- The actual affine parameter opens cover the scheme locus. -/
theorem translatedSchemeLocus_affine_covers (z : translatedSchemeLocus f hL) :
    ∃ j : TranslatedLocusAffineIndex f,
      ∃ y : j.2.val.toScheme, translatedParameterToSchemeLocus f hL j.1 j.2.val y = z := by
  obtain ⟨i, hi⟩ := (mem_translatedSchemeLocusOpen f hL z.val).mp z.property
  obtain ⟨W, hW, y, hy⟩ := translatedOrbitOpen_exists_affine f hL i ⟨z.val, hi⟩
  refine ⟨⟨i, W, hW⟩, y, ?_⟩
  apply Subtype.ext
  have he := congrArg (fun k : W.toScheme.toLocallyRingedSpace ⟶
      invariantLocallyRingedSpace (smoothHilbertEquivalenceRelation f hL) ↦ k.base y)
    (translatedParameterToSchemeLocus_comp f hL i W)
  exact he.trans hy

/-- An actual affine-domain open cover of the original invariant scheme locus. -/
def translatedSchemeLocusAffineCover : (translatedSchemeLocus f hL).OpenCover :=
  Scheme.Cover.mkOfCovers (P := @IsOpenImmersion) (TranslatedLocusAffineIndex f)
    (fun j ↦ j.2.val.toScheme) (fun j ↦ translatedParameterToSchemeLocus f hL j.1 j.2.val)
    (translatedSchemeLocus_affine_covers f hL)

instance translatedSchemeLocusAffineCover_isAffine
    (j : (translatedSchemeLocusAffineCover f hL).I₀) :
    IsAffine ((translatedSchemeLocusAffineCover f hL).X j) := j.2.property

/-- Each original affine refinement is an affine open of the constructed scheme locus. -/
theorem translatedParameterToSchemeLocus_isAffineOpen
    (j : TranslatedLocusAffineIndex f) :
    IsAffineOpen (translatedParameterToSchemeLocus f hL j.1 j.2.val).opensRange := by
  let _ : IsAffine j.2.val.toScheme := j.2.property
  exact isAffineOpen_opensRange _

end FLT.Mazur.HilbertChart
