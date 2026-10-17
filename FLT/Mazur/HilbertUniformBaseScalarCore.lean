/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertUniformPrincipalCore
public import FLT.Mazur.RelativeRelationBaseFiberPrincipal

/-!
# Constructed base-scalar coverage inside the uniform principal core

Whole original base fibers inside uniform chart images supply genuine original
invariant principal neighborhoods. Their union is constructed independently of
the boundary section. Its inclusion in the principal core is proved, while
coverage of all original boundary points remains a separate geometric problem.
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

local notation "b" => invariantLocallyRingedBaseMap eo
local notation "Base" => Spec (.of R)

/-- Each actual chart gives a base open avoiding the closure of its bad source image. -/
def uniformBaseFiberOpen (a : Charts) : (Base).Opens :=
  baseFiberOpen eo W (uniformOrbitOpen f hL d V c k W a)

/-- The original orbit region covered by base scalars from actual uniform charts. -/
def uniformBaseScalarCore : TopologicalSpace.Opens (Orbit eo) :=
  W ⊓ (TopologicalSpace.Opens.map (b).base).obj (⨆ a : Charts,
    uniformBaseFiberOpen f hL d V c k W a)

/-- Membership supplies an actual chart whose entire nearby base fibers lie in its image. -/
theorem mem_uniformBaseScalarCore (x : Orbit eo) :
    x ∈ uniformBaseScalarCore f hL d V c k W ↔
      x ∈ W ∧ ∃ a : Charts, (b).base x ∈ uniformBaseFiberOpen f hL d V c k W a := by
  change (x ∈ W ∧ (b).base x ∈ ⨆ a : Charts,
    uniformBaseFiberOpen f hL d V c k W a) ↔ _
  rw [TopologicalSpace.Opens.mem_iSup]

/-- A base function supported in the constructed base open is an original geometric scalar. -/
theorem uniformBaseSection_mem_scalars (a : Charts) (r : Γ(Base, ⊤))
    (hr : (Base).basicOpen r ≤ uniformBaseFiberOpen f hL d V c k W a) :
    invariantBaseSection eo W r ∈ uniformPrincipalScalars f hL d V c k W :=
  ⟨a, baseSection_principal_le_of_baseFiber eo W _ r hr⟩

/-- At every point of this region an original geometric denominator is constructed. -/
theorem uniformBaseScalarCore_denominator (x : Orbit eo)
    (hx : x ∈ uniformBaseScalarCore f hL d V c k W) :
    ∃ r : Γ(Base, ⊤),
      invariantBaseSection eo W r ∈ uniformPrincipalScalars f hL d V c k W ∧
      x ∈ invariantPrincipal eo W (invariantBaseSection eo W r) := by
  obtain ⟨hxW, a, ha⟩ := (mem_uniformBaseScalarCore f hL d V c k W x).mp hx
  obtain ⟨r, hr, hO⟩ := exists_baseSection_principal eo W
    (uniformOrbitOpen f hL d V c k W a) x hxW ha
  exact ⟨r, ⟨a, hO⟩, hr⟩

/-- The newly constructed region lies in the original principal core. -/
theorem uniformBaseScalarCore_le_principalCore :
    uniformBaseScalarCore f hL d V c k W ≤ uniformPrincipalCore f hL d V c k W := by
  intro x hx
  obtain ⟨r, hr, hx⟩ := uniformBaseScalarCore_denominator f hL d V c k W x hx
  exact (mem_uniformPrincipalCore f hL d V c k W x).mpr ⟨_, hr, hx⟩

/-- The region is exactly covered by base scalars with actual geometric chart support. -/
theorem uniformBaseScalarCore_eq_basePrincipalUnion :
    uniformBaseScalarCore f hL d V c k W =
      ⨆ r : {r : Γ(Base, ⊤) |
        invariantBaseSection eo W r ∈ uniformPrincipalScalars f hL d V c k W},
        invariantPrincipal eo W (invariantBaseSection eo W r.val) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨r, hr, hx⟩ := uniformBaseScalarCore_denominator f hL d V c k W x hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨r, hr⟩, hx⟩
  · apply iSup_le
    intro r x hx
    obtain ⟨a, ha⟩ := r.property
    rw [invariantPrincipal_baseSection] at hx
    apply (mem_uniformBaseScalarCore f hL d V c k W x).mpr
    refine ⟨hx.1, a, ?_⟩
    apply (baseOpen_le_baseFiberOpen_iff eo W _ ((Base).basicOpen r.val)).mpr ?_ hx.2
    rwa [← invariantPrincipal_baseSection]

end OrbitBoundaryAtlas
end FLT.Mazur.HilbertChart.AffineRestriction
