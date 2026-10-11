/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeRelationInvariantLocallyRinged
public import FLT.Mazur.RelativeRelationQuotientSections
public import FLT.Mazur.SmoothHilbertLocallyRingedQuotient

/-!
# The actual smooth Hilbert quotient has the invariant structure sheaf

The original Hilbert relation now has a quotient on its explicit orbit carrier,
with the invariant regular-function sheaf and proved local stalks. It agrees
with the previously constructed locally ringed coequalizer over the original
base. Affine quotient neighborhoods and scheme effectivity remain separate work.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.HilbertChart
open CartierAbel FCurve SchemePicard OrderedCurvePower RelativeRelationOrbit
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {B : X.Modules} (hB : AmpleLineBundle B)

/-- The actual smooth Hilbert orbit with its invariant sheaf and proved local stalks. -/
def smoothHilbertInvariantQuotient : LocallyRingedSpace :=
  invariantLocallyRingedSpace (smoothHilbertEquivalenceRelation f hB)

/-- The explicit invariant quotient is the previously constructed locally ringed coequalizer. -/
def smoothHilbertInvariantQuotientIso :
    smoothHilbertLocallyRingedQuotient f hB ≅ smoothHilbertInvariantQuotient f hB :=
  invariantLocallyRingedIso (smoothHilbertEquivalenceRelation f hB)

/-- The original Hilbert source maps to the explicit invariant quotient by a local morphism. -/
def smoothHilbertInvariantProjection :
    (smoothHilbertSource f).left.toLocallyRingedSpace ⟶ smoothHilbertInvariantQuotient f hB :=
  invariantLocallyRingedProjection (smoothHilbertEquivalenceRelation f hB)

/-- Its continuous map is exactly the original relation's orbit projection. -/
theorem smoothHilbertInvariantProjection_base :
    (smoothHilbertInvariantProjection f hB).base =
      quotientMap (smoothHilbertEquivalenceRelation f hB) :=
  invariantLocallyRingedProjection_base (smoothHilbertEquivalenceRelation f hB)

/-- The explicit invariant quotient retains the original base. -/
def smoothHilbertInvariantBaseMap : smoothHilbertInvariantQuotient f hB ⟶
    (Spec (.of R)).toLocallyRingedSpace :=
  invariantLocallyRingedBaseMap (smoothHilbertEquivalenceRelation f hB)

/-- The base map recovers the actual Hilbert source's structural morphism. -/
theorem smoothHilbertInvariantProjection_baseMap :
    smoothHilbertInvariantProjection f hB ≫ smoothHilbertInvariantBaseMap f hB =
      (smoothHilbertSource f).hom.toLRSHom :=
  invariantLocallyRingedProjection_baseMap (smoothHilbertEquivalenceRelation f hB)

/-- The quotient's actual structure sheaf is the original invariant-function sheaf. -/
def smoothHilbertInvariantStructureSheafIso :
    smoothHilbertOrbitInvariantSheaf f hB ≅
      (TopCat.Sheaf.pushforward _
        (locallyRingedOrbitIso (smoothHilbertEquivalenceRelation f hB)).hom).obj
          (smoothHilbertLocallyRingedQuotient f hB).toSheafedSpace.sheaf :=
  invariantSheafIsoCanonicalQuotient (smoothHilbertEquivalenceRelation f hB)

/-- The explicit invariant quotient projection is surjective on points. -/
theorem smoothHilbertInvariantProjection_surjective :
    Function.Surjective (smoothHilbertInvariantProjection f hB).base := by
  rw [smoothHilbertInvariantProjection_base]
  exact projection_surjective (smoothHilbertEquivalenceRelation f hB)

/-- Smoothness makes the explicit invariant quotient projection open. -/
theorem smoothHilbertInvariantProjection_isOpenMap :
    IsOpenMap (smoothHilbertInvariantProjection f hB).base := by
  rw [smoothHilbertInvariantProjection_base]
  exact projection_isOpenMap (smoothHilbertEquivalenceRelation f hB)
    (smoothHilbertRelationSnd f hB).left.isOpenMap

end FLT.Mazur.HilbertChart
