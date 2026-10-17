/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertUniformOriginalLiftingOpen
public import FLT.Mazur.HilbertUniformSourcePrincipalMultipliers

/-!
# Original scalars supported in uniform geometric chart images

The span uses actual original invariant sections with principal domains in a
constructed uniform chart image. It lies in the radical of every boundary
lifting ideal, independently of the chosen boundary section. No unit ideal
or coverage assertion is built into its definition.
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

/-- Actual original scalars with a geometric principal subneighborhood in one uniform chart. -/
def uniformPrincipalScalars : Set Ω :=
  {v | ∃ a : Charts, invariantPrincipal eo W v ≤ uniformOrbitOpen f hL d V c k W a}

/-- The scalar ideal constructed before choosing a boundary section. -/
def uniformPrincipalIdeal : Ideal Ω := Ideal.span (uniformPrincipalScalars f hL d V c k W)

/-- Each geometric scalar has a finite power which lifts every given boundary section. -/
theorem uniformPrincipalScalars_power_lift
    (hW : IsAffineOpen (pullOpen eo W).val) (v : Ω)
    (hv : v ∈ uniformPrincipalScalars f hL d V c k W)
    (t : (invariantSheaf ec).obj.obj (op Wc)) :
    ∃ (N : ℕ) (b : Ω), (m).c.app (op W) b =
      originalClosedSectionPullback f hL d V c k W v ^ N * t := by
  obtain ⟨a, ha⟩ := hv
  exact uniformSource_original_power_lift f hL d V c k a.size a.label a.domain
    a.stable W a.overDomain a.affine hW v ha t

/-- Every geometric scalar lies in the radical of each fixed-domain boundary lifting ideal. -/
theorem uniformPrincipalScalars_mem_radical
    (hW : IsAffineOpen (pullOpen eo W).val) (v : Ω)
    (hv : v ∈ uniformPrincipalScalars f hL d V c k W)
    (t : (invariantSheaf ec).obj.obj (op Wc)) :
    v ∈ (originalBoundaryLiftIdeal f hL d V c k W t).radical := by
  obtain ⟨N, b, hb⟩ := uniformPrincipalScalars_power_lift f hL d V c k W hW v hv t
  apply (originalBoundaryLiftIdeal_radical_iff f hL d V c k W t hW v).mpr
  exact ⟨N, (originalClosedSectionObstruction_eq_zero_iff
    f hL d V c k W hW _).mpr ⟨b, hb⟩⟩

/-- Arbitrary original linear combinations remain in every boundary lifting radical. -/
theorem uniformPrincipalIdeal_le_radical
    (hW : IsAffineOpen (pullOpen eo W).val)
    (t : (invariantSheaf ec).obj.obj (op Wc)) :
    uniformPrincipalIdeal f hL d V c k W ≤
      (originalBoundaryLiftIdeal f hL d V c k W t).radical := by
  apply Ideal.span_le.mpr
  intro v hv
  exact uniformPrincipalScalars_mem_radical f hL d V c k W hW v hv t

end OrbitBoundaryAtlas
end FLT.Mazur.HilbertChart.AffineRestriction
