/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertUniformPrincipalCore
public import FLT.Mazur.HilbertUniformPrincipalErrorSupport
public import FLT.Mazur.HilbertBoundaryLocalCoverCriterion
public import FLT.Mazur.LocallyRingedIdealGenerators

/-!
# Exact geometric coverage criterion for the original principal core

The principal core is exactly the unit locus of the constructed invariant
scalar ideal. Its inverse image covers the whole original boundary domain
precisely when the actual boundary source image ideal is the unit ideal.
This identifies the remaining coverage obligation without assuming it.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve EquivalenceRelationNormalizedFrames
open RelativeRelationOrbit InvariantOpenRelationDiagram
open FiniteGroupRestriction SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [IsAffine V.left] [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
local notation "p" => Over.Hom.left (AffineRestriction.fst f hL d V c k)
local notation "q" => Over.Hom.left (AffineRestriction.snd f hL d V c k)
local notation "e" => fullRelationSchemeEquivalence f hL d V c k
local notation "eo" => equivalence f hL d V c k
local notation "ec" => originalClosedEquivalence f hL d V c k
local notation "m" => originalClosedInvariantMap f hL d V c k
attribute [local irreducible] relation AffineRestriction.fst AffineRestriction.snd equivalence
  EquivalenceRelationNormalizedFrames.source relativeFppfSheaf AmpleLineBundle
  originalBoundarySource originalBoundarySourceMap originalClosedRelation
  originalClosedFst originalClosedSnd originalClosedArrow originalClosedEquivalence
namespace OrbitBoundaryAtlas
variable (W : TopologicalSpace.Opens (Orbit (equivalence f hL d V c k)))
attribute [local irreducible] EquivalenceRelationNormalizedFrames.action
  uniformSourceOpen orbitImageOpen etaleSourceImage
set_option quotPrecheck false
local notation "Wc" => (TopologicalSpace.Opens.map (m).base).obj W
local notation "Charts" => Chart f hL d V c k W

local notation "Ω" => (invariantSheaf eo).obj.obj (op W)

local notation "J" => uniformPrincipalIdeal f hL d V c k W

/-- Taking the ideal span adds no points to the original geometric principal core. -/
theorem uniformPrincipalCore_eq_idealOpen :
    uniformPrincipalCore f hL d V c k W = sectionIdealOpen (ringedSpace eo) W J :=
  (sectionIdealOpen_span_generators (invariantLocallyRingedSpace eo) W
    (uniformPrincipalScalars f hL d V c k W)).symm

/-- Full boundary coverage by the principal core is exactly the constructed source unit test. -/
theorem uniformPrincipalCore_boundary_cover_iff
    (hW : IsAffineOpen (pullOpen eo W).val) :
    (TopologicalSpace.Opens.map (m).base).obj
        (uniformPrincipalCore f hL d V c k W) = Wc ↔
      uniformPrincipalBoundaryIdeal f hL d V c k W = ⊤ := by
  rw [uniformPrincipalCore_eq_idealOpen]
  exact preimage_sectionIdealOpen_eq_iff_sourceIdeal_top eo ec
    (originalBoundarySourceMap f hL d V c k).left
    (originalClosedArrow f hL d V c k).left
    (originalClosedArrow_left_fst f hL d V c k)
    (originalClosedArrow_left_snd f hL d V c k) W J
    (originalBoundaryLift_closedSource_affine f hL d V c k W hW)

end OrbitBoundaryAtlas
end FLT.Mazur.HilbertChart.AffineRestriction
