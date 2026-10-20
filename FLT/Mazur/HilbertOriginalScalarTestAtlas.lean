/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeScalarFullAtlas
public import FLT.Mazur.HilbertScalarChartBoundaryTests
public import FLT.Mazur.HilbertOrbitBoundaryFiniteScalars
public import FLT.Mazur.InvariantOpenRelationEquivalence
public import FLT.Mazur.SchemeScalarAvoidanceCover

/-!
# The whole original Hilbert source on every scalar test

The original invariant scalars define both full relation endpoints. Pulling
back the old finite atlas covers the entire original scalar-test source,
without imposing a whole-complete locus or identifying distinct orbits.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Topology
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve EquivalenceRelationNormalizedFrames
open FiniteGroupRestriction SchemeFiniteGroupQuotient SchemeOpenEnvelope
open RelativeRelationOrbit SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [IsAffine V.left] [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
local notation "p" => Over.Hom.left (fst f hL d V c k)
local notation "q" => Over.Hom.left (snd f hL d V c k)
local notation "e" => fullRelationSchemeEquivalence f hL d V c k
attribute [local irreducible] relation fst snd equivalence

local notation "eo" => equivalence f hL d V c k
variable (W : TopologicalSpace.Opens (Orbit (equivalence f hL d V c k)))
set_option quotPrecheck false
local notation "E" => (pullOpen eo W).val
local notation "Ω" => (invariantSheaf eo).obj.obj (op W)
local notation "s" => orbitScalarCoordinates eo W

attribute [local irreducible] invariantSheaf orbitScalarCoordinates
  EquivalenceRelationNormalizedFrames.source first completeInterior Complete
  scalarMorphism finiteTargetOpen

local notation "ec" => originalClosedEquivalence f hL d V c k
local notation "m" => originalClosedInvariantMap f hL d V c k
local notation "Wc" => (TopologicalSpace.Opens.map (m).base).obj W
attribute [local irreducible] originalClosedEquivalence
  normalizedOriginalBoundaryAction
  normalizedOriginalScalarMap

namespace OriginalScalarSource
open SchemeScalarRelationPullback

/-- The first endpoint of the full original relation restricted to the orbit domain. -/
abbrev first := (InvariantOpenRelationDiagram.fst (fst f hL d V c k) E).left

/-- The independent second endpoint of that same entire relation. -/
abbrev second := (InvariantOpenRelationDiagram.snd (fst f hL d V c k)
  (snd f hL d V c k) E (pullOpen_preimage_eq eo W)).left

/-- The actual equivalence operations on the unchanged original source domain. -/
def fullEquivalence : CategoryTheory.EquivalenceRelation
    (first f hL d V c k W) (second f hL d V c k W) :=
  InvariantOpenRelationDiagram.schemeEquivalence (fst f hL d V c k)
    (snd f hL d V c k) e E (pullOpen_preimage_eq eo W)

omit [IsAffine V.left] [Etale V.hom] [IsAffine A.left] [IsOpenImmersion k.left] in
/-- The full original relation lies over the unchanged invariant scalar spectrum. -/
theorem scalar_square :
    first f hL d V c k W ≫ scalarMorphism s =
      second f hL d V c k W ≫ scalarMorphism s := by
  rw [← scalarMorphism_comp, ← scalarMorphism_comp]
  congr 1
  ext a
  change (first f hL d V c k W).appTop (s a) =
    (second f hL d V c k W).appTop (s a)
  rw [orbitScalarCoordinates_apply]
  simpa only [first, second, InvariantOpenRelationDiagram.fst,
    InvariantOpenRelationDiagram.snd, Scheme.Hom.resLE_eq_morphismRestrict,
    InvariantOpenRelationDiagram.relation, InvariantOpenRelationDiagram.source,
    Over.homMk_left, Over.mk_left] using
    OrbitBoundaryAtlas.FiniteAtlas.original_scalar_equalized f hL d V c k W a

variable {Y : Scheme} (b : Y ⟶ Spec (.of
  ((invariantSheaf (equivalence f hL d V c k)).obj.obj (op W))))

/-- The full original scalar-test equalizer, before any atlas restriction. -/
abbrev testRing := testInvariants (first f hL d V c k W) (second f hL d V c k W)
  (scalarMorphism s) (scalar_square f hL d V c k W) b

variable (hW : IsAffineOpen (pullOpen (equivalence f hL d V c k) W).val)

/-- A finite actual fppf atlas covering the entire original scalar-test source. -/
abbrev atlas : (testSource (scalarMorphism s) b).Cover Scheme.fppfPrecoverage :=
  fullAtlas (scalarMorphism s) b (OrbitBoundaryAtlas.finiteFppfCover f hL d V c k W hW)

/-- The unchanged finite atlas index works for every scalar test. -/
instance atlasFintype : Fintype (atlas f hL d V c k W b hW).I₀ :=
  inferInstanceAs (Fintype (OrbitBoundaryAtlas.finiteFppfCover f hL d V c k W hW).I₀)

/-- Every original scalar-test point, rather than only a chosen chart, is covered. -/
theorem atlas_covers (x : testSource (scalarMorphism s) b) :
    ∃ a, ∃ z : (atlas f hL d V c k W b hW).X a,
      (atlas f hL d V c k W b hW).f a z = x :=
  fullAtlas_covers (scalarMorphism s) b
    (OrbitBoundaryAtlas.finiteFppfCover f hL d V c k W hW) x

/-- Full mixed-compatible test coefficients descend to the original equalizer uniquely. -/
theorem atlas_invariants_descend
    (v : ∀ a, Γ((atlas f hL d V c k W b hW).X a, ⊤))
    (hv : SchemeFppfRelationDescent.Compatible
      (testFirst (first f hL d V c k W) (scalarMorphism s) b)
      (testSecond (first f hL d V c k W) (second f hL d V c k W)
        (scalarMorphism s) (scalar_square f hL d V c k W) b)
      (atlas f hL d V c k W b hW) v) :
    ∃! t : testRing f hL d V c k W b,
      ∀ a, ((atlas f hL d V c k W b hW).f a).appTop t.val = v a := by
  let er := fullEquivalence f hL d V c k W
  exact fullAtlas_invariants_descend _ _ _ _ b
    (OrbitBoundaryAtlas.finiteFppfCover f hL d V c k W hW)
    er.r er.reflexivity₁ er.reflexivity₂ v hv

end OriginalScalarSource
end FLT.Mazur.HilbertChart.AffineRestriction
