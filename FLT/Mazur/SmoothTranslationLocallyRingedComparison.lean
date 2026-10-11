/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SmoothTranslationInvariantSheafComparison
public import FLT.Mazur.RelativeRelationInvariantLocallyRinged

/-!
# The full chart quotient is the original locally ringed neighborhood

The actual invariant sheaf comparison upgrades the quotient homeomorphism to a
locally ringed space isomorphism. Affine charts are still a separate obligation.
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

/-- The actual chart ringed quotient is the actual original ringed neighborhood. -/
def smoothTranslationInvariantRingedIso :
    ringedSpace (variableChartEquivalenceRelation f hL d V c) ≅
      smoothTranslationOriginalRingedNeighborhood f hL d V c :=
  SheafedSpace.isoMk (PresheafedSpace.isoOfComponents
    (smoothTranslationChartTopIso f hL d V c)
    (smoothTranslationInvariantPresheafIso f hL d V c).symm)

/-- The ringed comparison retains the already proved orbit-space homeomorphism. -/
theorem smoothTranslationInvariantRingedIso_base :
    (smoothTranslationInvariantRingedIso f hL d V c).hom.hom.base =
      (smoothTranslationChartTopIso f hL d V c).hom := rfl

/-- The original invariant locally ringed space restricted to its translation neighborhood. -/
def smoothTranslationOriginalLocallyRingedNeighborhood : LocallyRingedSpace :=
  (invariantLocallyRingedSpace (smoothHilbertEquivalenceRelation f hL)).restrict
    (TopologicalSpace.Opens.isOpenEmbedding
      (X := space (smoothHilbertEquivalenceRelation f hL))
      (smoothTranslationOrbitOpen f hL d V c))

/-- The full chart's actual locally ringed quotient is the original quotient neighborhood. -/
def smoothTranslationInvariantLocallyRingedIso :
    invariantLocallyRingedSpace (variableChartEquivalenceRelation f hL d V c) ≅
      smoothTranslationOriginalLocallyRingedNeighborhood f hL d V c :=
  LocallyRingedSpace.isoOfSheafedSpaceIso (smoothTranslationInvariantRingedIso f hL d V c)

/-- The locally ringed comparison retains the original topological comparison. -/
theorem smoothTranslationInvariantLocallyRingedIso_base :
    (smoothTranslationInvariantLocallyRingedIso f hL d V c).hom.base =
      (smoothTranslationChartTopIso f hL d V c).hom := rfl

/-- Each original neighborhood section pulls back by the constructed section-ring comparison. -/
theorem smoothTranslationInvariantLocallyRingedIso_app
    (W : TopologicalSpace.Opens (smoothTranslationNeighborhood f hL d V c)) :
    (smoothTranslationInvariantLocallyRingedIso f hL d V c).hom.c.app (op W) =
      (smoothTranslationNeighborhoodSectionIso f hL d V c W).hom := rfl

end FLT.Mazur.HilbertChart
