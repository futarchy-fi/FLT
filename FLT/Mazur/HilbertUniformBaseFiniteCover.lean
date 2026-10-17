/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertUniformBaseScalarCore

/-!
# Finite base denominators for the constructed uniform coverage region

Noetherianity of the original affine base produces finitely many actual base
functions whose basic opens cover the whole constructed base region. Their
original invariant pullbacks cover its orbit preimage, and each has a power
lift for every fixed-domain boundary section. No unit-ideal identity is assumed.
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

/-- Base functions whose whole source fibers lie in one actual uniform chart image. -/
def uniformBaseScalars : Set Γ(Base, ⊤) :=
  {r | ∃ a : Charts, (Base).basicOpen r ≤ uniformBaseFiberOpen f hL d V c k W a}

local notation "Scalars" => uniformBaseScalars f hL d V c k W
local notation "B" => (⨆ a : Charts, uniformBaseFiberOpen f hL d V c k W a : (Base).Opens)

/-- Every point of the constructed base open has a base function with actual chart support. -/
theorem uniformBaseOpen_eq_principalUnion :
    (B) = ⨆ r : Scalars, (Base).basicOpen r.val := by
  apply le_antisymm
  · intro x hx
    obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    obtain ⟨r, hr, hO⟩ := AffineEnvelopeFiniteNeighborhood.exists_envelope_principal
      (uniformBaseFiberOpen f hL d V c k W a) {x} (Set.finite_singleton _)
      (by simpa using ha)
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨r, a, hO⟩, hr (Set.mem_singleton _)⟩
  · apply iSup_le
    rintro ⟨r, a, ha⟩ x hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨a, ha hx⟩

/-- Finitely many actual base functions cover the entire constructed base region. -/
theorem uniformBaseOpen_finite_cover :
    ∃ indices : Finset Scalars, ((B) : Set (Base)) =
      ⋃ r ∈ indices, ((Base).basicOpen r.val : Set (Base)) := by
  let _ : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  have hc := TopologicalSpace.NoetherianSpace.isCompact ((B) : Set (Base))
  obtain ⟨indices, hi⟩ := hc.elim_finite_subcover
    (fun r : Scalars ↦ ((Base).basicOpen r.val : Set (Base)))
    (fun r ↦ ((Base).basicOpen r.val).isOpen) (by
      intro x hx
      rw [uniformBaseOpen_eq_principalUnion] at hx
      obtain ⟨r, hr⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
      exact Set.mem_iUnion.mpr ⟨r, hr⟩)
  refine ⟨indices, Set.Subset.antisymm hi ?_⟩
  intro x hx
  obtain ⟨r, _, hx⟩ := Set.mem_iUnion₂.mp hx
  obtain ⟨a, ha⟩ := r.property
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨a, ha hx⟩

/-- One finite list of original base scalars covers the orbit region and gives power lifts. -/
theorem uniformBaseScalarCore_finite_power_lifts
    (hW : IsAffineOpen (pullOpen eo W).val) :
    ∃ indices : Finset Scalars,
      (uniformBaseScalarCore f hL d V c k W : Set (Orbit eo)) =
        ⋃ r ∈ indices, (invariantPrincipal eo W
          (invariantBaseSection eo W r.val) : Set (Orbit eo)) ∧
      ∀ r ∈ indices, ∀ t : (invariantSheaf ec).obj.obj (op Wc),
        ∃ (N : ℕ) (v : Ω), (m).c.app (op W) v =
          originalClosedSectionPullback f hL d V c k W
            (invariantBaseSection eo W r.val) ^ N * t := by
  obtain ⟨indices, hi⟩ := uniformBaseOpen_finite_cover f hL d V c k W
  refine ⟨indices, ?_, ?_⟩
  · ext x
    simp only [Set.mem_iUnion, SetLike.mem_coe]
    constructor
    · intro hx
      change x ∈ W ∧ (b).base x ∈ (B) at hx
      have hb : (b).base x ∈ ⋃ r ∈ indices,
          ((Base).basicOpen r.val : Set (Base)) := hi ▸ hx.2
      obtain ⟨r, hr, hxr⟩ := Set.mem_iUnion₂.mp hb
      refine ⟨r, hr, ?_⟩
      rw [invariantPrincipal_baseSection]
      exact ⟨hx.1, hxr⟩
    · rintro ⟨r, hr, hx⟩
      rw [invariantPrincipal_baseSection] at hx
      change x ∈ W ∧ (b).base x ∈ (B)
      exact ⟨hx.1, (Set.ext_iff.mp hi ((b).base x)).mpr
        (Set.mem_iUnion₂.mpr ⟨r, hr, hx.2⟩)⟩
  · intro r _ t
    obtain ⟨a, ha⟩ := r.property
    exact uniformPrincipalScalars_power_lift f hL d V c k W hW _
      (uniformBaseSection_mem_scalars f hL d V c k W a r.val ha) t

end OrbitBoundaryAtlas
end FLT.Mazur.HilbertChart.AffineRestriction
