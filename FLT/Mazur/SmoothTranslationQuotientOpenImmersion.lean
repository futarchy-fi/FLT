/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SmoothTranslationLocallyRingedComparison
public import Mathlib.Geometry.RingedSpace.OpenImmersion

/-!
# Full chart quotients embed openly in the original locally ringed quotient

The constructed invariant sheaf isomorphism supplies an actual open immersion,
whose image is precisely the smooth translation neighborhood.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve RelativeRelationOrbit
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [Smooth V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))

/-- The full chart's locally ringed quotient maps into the original locally ringed quotient. -/
def smoothTranslationQuotientInclusion :
    invariantLocallyRingedSpace (variableChartEquivalenceRelation f hL d V c) ⟶
      invariantLocallyRingedSpace (smoothHilbertEquivalenceRelation f hL) :=
  (smoothTranslationInvariantLocallyRingedIso f hL d V c).hom ≫
    (invariantLocallyRingedSpace (smoothHilbertEquivalenceRelation f hL)).ofRestrict
      (TopologicalSpace.Opens.isOpenEmbedding
        (X := space (smoothHilbertEquivalenceRelation f hL))
        (smoothTranslationOrbitOpen f hL d V c))

/-- The inclusion is an open immersion of the actual locally ringed quotients. -/
instance smoothTranslationQuotientInclusion_isOpenImmersion :
    LocallyRingedSpace.IsOpenImmersion (smoothTranslationQuotientInclusion f hL d V c) := by
  dsimp only [smoothTranslationQuotientInclusion]
  infer_instance

/-- Its underlying map is the original chart orbit map. -/
theorem smoothTranslationQuotientInclusion_base :
    (smoothTranslationQuotientInclusion f hL d V c).base =
      smoothTranslationChartOrbitMap f hL d V c := rfl

/-- The original parameter points are retained by the locally ringed quotient inclusion. -/
theorem smoothTranslationQuotientInclusion_projection (x : (variableHilbertTest f d V).left) :
    (smoothTranslationQuotientInclusion f hL d V c).base
      (projection (variableChartEquivalenceRelation f hL d V c) x) =
        (smoothTranslationChartToOrbit f hL d V c x).val :=
  smoothTranslationChartOrbitMap_projection f hL d V c x

/-- The image is exactly the constructed original translation neighborhood. -/
theorem smoothTranslationQuotientInclusion_range :
    Set.range (smoothTranslationQuotientInclusion f hL d V c).base =
      (smoothTranslationOrbitOpen f hL d V c :
        Set (Orbit (smoothHilbertEquivalenceRelation f hL))) := by
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    exact (smoothTranslationChartOrbitToOpen f hL d V c w).property
  · intro hz
    obtain ⟨w, hw⟩ := (smoothTranslationChartOrbitHomeomorph f hL d V c).surjective ⟨z, hz⟩
    exact ⟨w, congrArg Subtype.val hw⟩

end FLT.Mazur.HilbertChart
