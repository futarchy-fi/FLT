/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertUniformPrincipalScalarIdeal
public import FLT.Mazur.HilbertBoundaryFiniteLiftCover

/-!
# A finite original principal core of the uniform lifting domain

The core is the union of original principal opens actually contained in one
uniform chart image. Noetherian topology gives a finite cover by such scalars;
each yields a fixed-domain power lift for every boundary section. The core
is not asserted to equal the uniform lifting domain or the original domain.
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

local notation "S" => uniformPrincipalScalars f hL d V c k W

/-- The original principal core, constructed without choosing a boundary section. -/
def uniformPrincipalCore : TopologicalSpace.Opens (Orbit eo) :=
  ⨆ v : S, invariantPrincipal eo W v.val

/-- Every point of the core has an actual geometric scalar witness. -/
theorem mem_uniformPrincipalCore (x : Orbit eo) :
    x ∈ uniformPrincipalCore f hL d V c k W ↔
      ∃ v ∈ S, x ∈ invariantPrincipal eo W v := by
  simp only [uniformPrincipalCore, TopologicalSpace.Opens.mem_iSup,
    Subtype.exists, exists_prop]

/-- The core stays inside the constructed uniform orbit-image domain. -/
theorem uniformPrincipalCore_le_uniformLiftingOpen :
    uniformPrincipalCore f hL d V c k W ≤ uniformLiftingOpen f hL d V c k W := by
  intro x hx
  obtain ⟨v, ⟨a, ha⟩, hxv⟩ := (mem_uniformPrincipalCore f hL d V c k W x).mp hx
  exact (mem_uniformLiftingOpen f hL d V c k W x).mpr ⟨a, ha hxv⟩

/-- Every fixed-domain boundary section lifts on the whole core in the multiplier sense. -/
theorem uniformPrincipalCore_le_boundaryLiftOpen
    (hW : IsAffineOpen (pullOpen eo W).val)
    (t : (invariantSheaf ec).obj.obj (op Wc)) :
    uniformPrincipalCore f hL d V c k W ≤ originalBoundaryLiftOpen f hL d V c k W t := by
  intro x hx
  obtain ⟨v, ⟨a, ha⟩, hxv⟩ := (mem_uniformPrincipalCore f hL d V c k W x).mp hx
  exact uniformSource_original_principal_le_liftOpen f hL d V c k
    a.size a.label a.domain a.stable W a.overDomain a.affine hW v ha t hxv

/-- Finitely many original geometric scalars cover the full constructed principal core. -/
theorem uniformPrincipalCore_finite_cover :
    ∃ indices : Finset S, (uniformPrincipalCore f hL d V c k W : Set (Orbit eo)) =
      ⋃ v ∈ indices, (invariantPrincipal eo W v.val : Set (Orbit eo)) := by
  let _ := originalOrbit_noetherianSpace f hL d V c k
  have hc := TopologicalSpace.NoetherianSpace.isCompact
    (uniformPrincipalCore f hL d V c k W : Set (Orbit eo))
  obtain ⟨indices, hi⟩ := hc.elim_finite_subcover
    (fun v : S ↦ (invariantPrincipal eo W v.val : Set (Orbit eo)))
    (fun v ↦ (invariantPrincipal eo W v.val).isOpen) (by
      intro x hx
      obtain ⟨v, hv, hxv⟩ := (mem_uniformPrincipalCore f hL d V c k W x).mp hx
      exact Set.mem_iUnion.mpr ⟨⟨v, hv⟩, hxv⟩)
  refine ⟨indices, Set.Subset.antisymm hi ?_⟩
  intro x hx
  obtain ⟨v, _, hxv⟩ := Set.mem_iUnion₂.mp hx
  exact (mem_uniformPrincipalCore f hL d V c k W x).mpr ⟨v.val, v.property, hxv⟩

/-- One finite original scalar cover supplies power lifts for every fixed-domain section. -/
theorem uniformPrincipalCore_finite_power_lifts
    (hW : IsAffineOpen (pullOpen eo W).val) :
    ∃ indices : Finset S, (uniformPrincipalCore f hL d V c k W : Set (Orbit eo)) =
        ⋃ v ∈ indices, (invariantPrincipal eo W v.val : Set (Orbit eo)) ∧
      ∀ v ∈ indices, ∀ t : (invariantSheaf ec).obj.obj (op Wc),
        ∃ (N : ℕ) (b : Ω), (m).c.app (op W) b =
          originalClosedSectionPullback f hL d V c k W v.val ^ N * t := by
  obtain ⟨indices, hi⟩ := uniformPrincipalCore_finite_cover f hL d V c k W
  exact ⟨indices, hi, fun v _ t ↦
    uniformPrincipalScalars_power_lift f hL d V c k W hW v.val v.property t⟩

end OrbitBoundaryAtlas
end FLT.Mazur.HilbertChart.AffineRestriction
