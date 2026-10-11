/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LocallyRingedSchemeChartUnion
public import FLT.Mazur.TranslatedHilbertAffineRestriction

/-!
# The actual translated-chart scheme locus of the original invariant quotient

The union of all constructed translated chart opens is a scheme with the
original invariant structure sheaf. Its parameter charts cover by construction.
This identifies a genuine open scheme locus; it does not claim that the locus
is the entire quotient over the arbitrary original base.
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

/-- The actual open locus covered by the constructed global-base translated charts. -/
def translatedSchemeLocusOpen : Opens (Orbit (smoothHilbertEquivalenceRelation f hL)) :=
  LocallyRingedSchemeChartUnion.chartUnion
    (fun i : TranslatedHilbertIndex f ↦ (⊤ : (acyclicHilbertTest f i.1).left.Opens).toScheme)
    (fun i ↦ translatedParameterOpenImmersion f hL i ⊤)

/-- The full parameter scheme gives precisely the original translated chart open. -/
theorem translatedChartOrbitOpens_top (i : TranslatedHilbertIndex f) :
    (translatedChartOrbitOpens f hL i).obj ⊤ = translatedOrbitOpen f hL i := by
  apply le_antisymm (translatedChartOrbitOpens_le f hL i ⊤)
  intro z hz
  exact ⟨⟨z, hz⟩, trivial, rfl⟩

/-- The constructed locus is exactly the union of the original translated quotient opens. -/
theorem translatedSchemeLocusOpen_eq_iSup :
    translatedSchemeLocusOpen f hL = ⨆ i, translatedOrbitOpen f hL i := by
  unfold translatedSchemeLocusOpen LocallyRingedSchemeChartUnion.chartUnion
  congr 1
  funext i
  apply Opens.ext
  exact (translatedParameterOpenImmersion_range f hL i ⊤).trans
    (congrArg (fun W : Opens (Orbit (smoothHilbertEquivalenceRelation f hL)) ↦ W.carrier)
      (translatedChartOrbitOpens_top f hL i))

/-- Membership in this scheme locus is membership in some constructed translated chart. -/
theorem mem_translatedSchemeLocusOpen
    (z : Orbit (smoothHilbertEquivalenceRelation f hL)) :
    z ∈ translatedSchemeLocusOpen f hL ↔ ∃ i, z ∈ translatedOrbitOpen f hL i := by
  rw [translatedSchemeLocusOpen_eq_iSup]
  exact Opens.mem_iSup

/-- The original source preimage is exactly the union of the actual chart intersections. -/
theorem translatedSchemeLocusOpen_source (x : (smoothHilbertSource f).left) :
    projection (smoothHilbertEquivalenceRelation f hL) x ∈ translatedSchemeLocusOpen f hL ↔
      ∃ i, x ∈ translatedSourceOpen f hL i := by
  rw [mem_translatedSchemeLocusOpen]
  exact exists_congr fun i ↦ mem_translatedOrbitOpen_iff f hL i x

/-- The scheme on the actual locus carries the original restricted invariant sheaf. -/
def translatedSchemeLocus : Scheme :=
  LocallyRingedSchemeChartUnion.scheme
    (fun i : TranslatedHilbertIndex f ↦ (⊤ : (acyclicHilbertTest f i.1).left.Opens).toScheme)
    (fun i ↦ translatedParameterOpenImmersion f hL i ⊤)

/-- No structure sheaf is replaced when constructing the scheme locus. -/
theorem translatedSchemeLocus_toLocallyRingedSpace :
    (translatedSchemeLocus f hL).toLocallyRingedSpace =
      invariantOpenSpace (smoothHilbertEquivalenceRelation f hL)
        (translatedSchemeLocusOpen f hL) := rfl

/-- The scheme locus includes into the original invariant quotient. -/
def translatedSchemeLocusInclusion : (translatedSchemeLocus f hL).toLocallyRingedSpace ⟶
    invariantLocallyRingedSpace (smoothHilbertEquivalenceRelation f hL) :=
  (invariantLocallyRingedSpace (smoothHilbertEquivalenceRelation f hL)).ofRestrict
    (Opens.isOpenEmbedding (X := space (smoothHilbertEquivalenceRelation f hL))
      (translatedSchemeLocusOpen f hL))

instance translatedSchemeLocusInclusion_isOpenImmersion :
    LocallyRingedSpace.IsOpenImmersion (translatedSchemeLocusInclusion f hL) := by
  delta translatedSchemeLocusInclusion
  infer_instance

/-- The constructed scheme retains the original relative base. -/
def translatedSchemeLocusBase : translatedSchemeLocus f hL ⟶ Spec (.of R) :=
  ⟨translatedSchemeLocusInclusion f hL ≫
    invariantLocallyRingedBaseMap (smoothHilbertEquivalenceRelation f hL)⟩

end FLT.Mazur.HilbertChart
