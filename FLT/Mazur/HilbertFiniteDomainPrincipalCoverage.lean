/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertFiniteRelationUniformCoverage
public import FLT.Mazur.HilbertUniformPrincipalCoreCoverage
public import FLT.Mazur.RelativeFiniteDomainPrincipal

/-!
# Original principal coverage on the exact finite target domain

Only the whole relation over the actual invariant source domain must be finite.
The ambient relation need not be finite. Complete original lifts and norm
scalars in the original sheaf cover this finite affine orbit domain.
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
  uniformSourceOpen orbitImageOpen etaleSourceImage SchemeOpenEnvelope.finiteTargetOpen
set_option quotPrecheck false
local notation "Wc" => (TopologicalSpace.Opens.map (m).base).obj W
local notation "Charts" => Chart f hL d V c k W

variable (hf : (pullOpen (equivalence f hL d V c k) W).val ≤
    SchemeOpenEnvelope.finiteTargetOpen (Over.Hom.left (AffineRestriction.fst f hL d V c k)))
  (ha : IsAffineOpen (pullOpen (equivalence f hL d V c k) W).val)

include hf in
omit [IsAffine V.left] [Etale V.hom] [IsAffine A.left] [IsOpenImmersion k.left] in
/-- Actual finite-domain membership is tested at an unchanged original source point. -/
theorem finiteDomain_mem (x : A.left) (hx : projection eo x ∈ W) :
    x ∈ SchemeOpenEnvelope.finiteTargetOpen p := by
  apply hf
  exact hx

include hf in
/-- Every point of the finite domain admits a complete original uniform lifting chart. -/
theorem uniformLiftingOpen_eq_of_finiteDomain :
    uniformLiftingOpen f hL d V c k W = W := by
  apply le_antisymm (uniformLiftingOpen_le f hL d V c k W)
  intro x hx
  obtain ⟨y, rfl⟩ := projection_surjective eo x
  exact projection_mem_uniformLiftingOpen_of_finiteTarget f hL d V c k W y hx
    (finiteDomain_mem f hL d V c k W hf y hx)

include hf ha in
/-- Local original sheaf norms refine every uniform chart inside the finite domain. -/
theorem uniformLiftingOpen_le_principalCore_of_finiteDomain :
    uniformLiftingOpen f hL d V c k W ≤ uniformPrincipalCore f hL d V c k W := by
  intro x hx
  obtain ⟨a, ha'⟩ := (mem_uniformLiftingOpen f hL d V c k W x).mp hx
  obtain ⟨s, hs, hsO⟩ := exists_invariantPrincipal_on_finiteOrbit eo e W hf ha
    (uniformOrbitOpen f hL d V c k W a)
    (uniformOrbitOpen_le f hL d V c k W a) x ha'
  exact (mem_uniformPrincipalCore f hL d V c k W x).mpr ⟨s, ⟨a, hsO⟩, hs⟩

include hf ha in
/-- Whole-preimage finiteness on the actual domain suffices for original principal coverage. -/
theorem uniformPrincipalCore_eq_of_finiteDomain :
    uniformPrincipalCore f hL d V c k W = W := by
  apply le_antisymm
  · exact (uniformPrincipalCore_le_uniformLiftingOpen f hL d V c k W).trans
      (uniformLiftingOpen_le f hL d V c k W)
  · exact (uniformLiftingOpen_eq_of_finiteDomain f hL d V c k W hf).ge.trans
      (uniformLiftingOpen_le_principalCore_of_finiteDomain f hL d V c k W hf ha)

include hf ha in
/-- The actual original boundary source scalar ideal is the unit ideal on this finite domain. -/
theorem uniformPrincipalBoundaryIdeal_eq_top_of_finiteDomain :
    uniformPrincipalBoundaryIdeal f hL d V c k W = ⊤ := by
  apply (uniformPrincipalCore_boundary_cover_iff f hL d V c k W ha).mp
  rw [uniformPrincipalCore_eq_of_finiteDomain f hL d V c k W hf ha]

end OrbitBoundaryAtlas
end FLT.Mazur.HilbertChart.AffineRestriction
