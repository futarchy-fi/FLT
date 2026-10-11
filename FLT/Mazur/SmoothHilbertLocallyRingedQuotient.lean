/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeRelationOrbitCoequalizer
public import FLT.Mazur.RelativeRelationInvariantSections
public import FLT.Mazur.SmoothHilbertRelationOperations
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# The actual locally ringed quotient of the smooth Hilbert relation

The represented Picard relation has a constructed locally ringed coequalizer
whose source map is open and surjective. Its point fibers are exactly the
original relation orbits. Local affineness and effective scheme descent are
still required; this object is not asserted to represent the Picard sheaf.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.HilbertChart
open CartierAbel FCurve SchemePicard OrderedCurvePower RelativeRelationOrbit
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {B : X.Modules} (hB : AmpleLineBundle B)

/-- The locally ringed coequalizer of the actual smooth Hilbert relation. -/
def smoothHilbertLocallyRingedQuotient : LocallyRingedSpace :=
  locallyRingedQuotient (p := smoothHilbertRelationFst f hB)
    (q := smoothHilbertRelationSnd f hB)

/-- The source map into the actual locally ringed quotient. -/
def smoothHilbertLocallyRingedProjection :
    (smoothHilbertSource f).left.toLocallyRingedSpace ⟶ smoothHilbertLocallyRingedQuotient f hB :=
  locallyRingedProjection

/-- The original relative base is retained as a locally ringed structural morphism. -/
def smoothHilbertLocallyRingedBaseMap :
    smoothHilbertLocallyRingedQuotient f hB ⟶ (Spec (.of R)).toLocallyRingedSpace :=
  locallyRingedBaseMap

/-- The locally ringed structural morphism recovers the original source structure map. -/
theorem smoothHilbertLocallyRingedProjection_baseMap :
    smoothHilbertLocallyRingedProjection f hB ≫ smoothHilbertLocallyRingedBaseMap f hB =
      (smoothHilbertSource f).hom.toLRSHom := locallyRingedProjection_baseMap

/-- The actual scheme relation is coequalized in locally ringed spaces. -/
theorem smoothHilbertLocallyRingedProjection_condition :
    (smoothHilbertRelationFst f hB).left.toLRSHom ≫ smoothHilbertLocallyRingedProjection f hB =
      (smoothHilbertRelationSnd f hB).left.toLRSHom ≫
        smoothHilbertLocallyRingedProjection f hB := coequalizer.condition _ _

/-- The quotient carrier is homeomorphic to the actual relation-orbit space. -/
def smoothHilbertLocallyRingedOrbitHomeomorph :
    smoothHilbertLocallyRingedQuotient f hB ≃ₜ Orbit (smoothHilbertEquivalenceRelation f hB) :=
  locallyRingedOrbitHomeomorph (smoothHilbertEquivalenceRelation f hB)

/-- Every locally ringed quotient point comes from an actual source point. -/
theorem smoothHilbertLocallyRingedProjection_surjective :
    Function.Surjective (smoothHilbertLocallyRingedProjection f hB).base :=
  locallyRingedProjection_surjective (smoothHilbertEquivalenceRelation f hB)

/-- The smooth relation makes the actual locally ringed quotient map open. -/
theorem smoothHilbertLocallyRingedProjection_isOpenMap :
    IsOpenMap (smoothHilbertLocallyRingedProjection f hB).base :=
  locallyRingedProjection_isOpenMap (smoothHilbertEquivalenceRelation f hB)
    (smoothHilbertRelationSnd f hB).left.isOpenMap

/-- Equality of quotient points is witnessed by an actual original relation point. -/
theorem smoothHilbertLocallyRingedProjection_eq_iff (x y : (smoothHilbertSource f).left) :
    (smoothHilbertLocallyRingedProjection f hB).base x =
      (smoothHilbertLocallyRingedProjection f hB).base y ↔
        ∃ a : (smoothHilbertRelation f hB).left,
          (smoothHilbertRelationFst f hB).left a = x ∧
            (smoothHilbertRelationSnd f hB).left a = y :=
  locallyRingedProjection_eq_iff (smoothHilbertEquivalenceRelation f hB) x y

/-- The actual quotient opens are exactly invariant opens on the original source scheme. -/
def smoothHilbertOrbitOpens :
    TopologicalSpace.Opens (Orbit (smoothHilbertEquivalenceRelation f hB)) ≃o
      InvariantOpens (smoothHilbertRelationFst f hB) (smoothHilbertRelationSnd f hB) :=
  opensOrderIso (smoothHilbertEquivalenceRelation f hB)

/-- The invariant regular-function sheaf constructed directly on the actual orbit space. -/
def smoothHilbertOrbitInvariantSheaf :
    (space (smoothHilbertEquivalenceRelation f hB)).Sheaf CommRingCat :=
  invariantSheaf (smoothHilbertEquivalenceRelation f hB)

/-- Any actual locally ringed morphism constant on the relation descends to this quotient. -/
def smoothHilbertLocallyRingedDescend {Z : LocallyRingedSpace}
    (a : (smoothHilbertSource f).left.toLocallyRingedSpace ⟶ Z)
    (ha : (smoothHilbertRelationFst f hB).left.toLRSHom ≫ a =
      (smoothHilbertRelationSnd f hB).left.toLRSHom ≫ a) :
    smoothHilbertLocallyRingedQuotient f hB ⟶ Z := coequalizer.desc a ha

/-- The descended morphism recovers the prescribed original source morphism. -/
theorem smoothHilbertLocallyRingedDescend_projection {Z : LocallyRingedSpace}
    (a : (smoothHilbertSource f).left.toLocallyRingedSpace ⟶ Z) (ha) :
    smoothHilbertLocallyRingedProjection f hB ≫ smoothHilbertLocallyRingedDescend f hB a ha = a :=
  coequalizer.π_desc _ _

end FLT.Mazur.HilbertChart
