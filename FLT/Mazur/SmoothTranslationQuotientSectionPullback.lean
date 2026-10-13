/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SmoothTranslationQuotientOpenImmersion

/-!
# Regular functions pulled back by the original quotient inclusion

Track the constructed inclusion on every original quotient open, including
restriction to its translation neighborhood and all domain transports.
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


local notation "e" => smoothHilbertEquivalenceRelation f hL
local notation "e'" => variableChartEquivalenceRelation f hL d V c
local notation "N" => smoothTranslationOrbitOpen f hL d V c
/-- The actual topological inclusion of the original translation neighborhood. -/
def smoothTranslationNeighborhoodInclusion :
    smoothTranslationNeighborhood f hL d V c ⟶ space e :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
local notation "i" => smoothTranslationNeighborhoodInclusion f hL d V c

/-- Restrict an original quotient open to the actual translation neighborhood. -/
def smoothTranslationInclusionDomain (O : TopologicalSpace.Opens (Orbit e)) :=
  smoothTranslationNeighborhoodOpen f hL d V c ((TopologicalSpace.Opens.map i).obj O)

/-- The restricted domain is contained in the original quotient open. -/
theorem smoothTranslationInclusionDomain_le (O : TopologicalSpace.Opens (Orbit e)) :
    smoothTranslationInclusionDomain f hL d V c O ≤ O := by
  rintro _ ⟨x, hx, rfl⟩
  exact hx

/-- On regular functions the inclusion is the original comparison after restriction. -/
theorem smoothTranslationQuotientInclusion_app
    (O : TopologicalSpace.Opens (Orbit e))
    (s : (invariantSheaf e).obj.obj (op O)) :
    (smoothTranslationQuotientInclusion f hL d V c).c.app (op O) s =
      (invariantSheaf e').obj.map
        (eqToHom (congrArg op (smoothTranslationNeighborhoodChartOpen_eq f hL d V c
          ((TopologicalSpace.Opens.map i).obj O))))
        (smoothTranslationInvariantSectionRingEquiv f hL d V c
          (smoothTranslationInclusionDomain f hL d V c O)
          (smoothTranslationNeighborhoodOpen_le f hL d V c _)
          ((invariantSheaf e).obj.map
            (homOfLE (smoothTranslationInclusionDomain_le f hL d V c O)).op s)) := by
  rfl

end FLT.Mazur.HilbertChart
