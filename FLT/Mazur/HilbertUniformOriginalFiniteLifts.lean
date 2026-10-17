/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertUniformOriginalLiftingOpen
public import FLT.Mazur.HilbertBoundaryFiniteLiftCover
public import FLT.Mazur.RelativeRelationEtaleSourceFunctions

/-!
# Finite coefficient-independent covers of the uniform lifting domain

Noetherianity extracts finitely many actual uniform orbit neighborhoods whose
union is the constructed lifting open. Each neighborhood lifts every boundary
section on the original fixed domain. This is not a cover of points outside
that constructed open, nor a finite generating family of invariant scalars.
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

local notation "N" => uniformLiftingOpen f hL d V c k W

/-- Finitely many actual uniform chart images cover the entire constructed lifting domain. -/
theorem uniformLiftingOpen_finite_cover :
    ∃ indices : Finset Charts, (N : Set (Orbit eo)) =
      ⋃ a ∈ indices, (uniformOrbitOpen f hL d V c k W a : Set (Orbit eo)) := by
  let _ := originalOrbit_noetherianSpace f hL d V c k
  have hcompact := TopologicalSpace.NoetherianSpace.isCompact (N : Set (Orbit eo))
  obtain ⟨indices, hi⟩ := hcompact.elim_finite_subcover
    (fun a : Charts ↦ (uniformOrbitOpen f hL d V c k W a : Set (Orbit eo)))
      (fun a ↦ (uniformOrbitOpen f hL d V c k W a).isOpen) (by
        intro x hx
        obtain ⟨a, ha⟩ := (mem_uniformLiftingOpen f hL d V c k W x).mp hx
        exact Set.mem_iUnion.mpr ⟨a, ha⟩)
  refine ⟨indices, Set.Subset.antisymm hi ?_⟩
  intro x hx
  obtain ⟨a, _, ha⟩ := Set.mem_iUnion₂.mp hx
  exact (mem_uniformLiftingOpen f hL d V c k W x).mpr ⟨a, ha⟩

/-- One finite geometric cover serves every original boundary section simultaneously. -/
theorem uniformLiftingOpen_finite_boundary_lifts :
    ∃ indices : Finset Charts, (N : Set (Orbit eo)) =
        ⋃ a ∈ indices, (uniformOrbitOpen f hL d V c k W a : Set (Orbit eo)) ∧
      ∀ a ∈ indices, ∀ t : (invariantSheaf ec).obj.obj (op Wc),
        ∃ b : (invariantSheaf eo).obj.obj (op (uniformOrbitOpen f hL d V c k W a)),
          (m).c.app (op (uniformOrbitOpen f hL d V c k W a)) b =
            (invariantSheaf ec).obj.map ((TopologicalSpace.Opens.map (m).base).map
              (homOfLE (uniformOrbitOpen_le f hL d V c k W a))).op t := by
  obtain ⟨indices, hi⟩ := uniformLiftingOpen_finite_cover f hL d V c k W
  exact ⟨indices, hi, fun a _ ↦ uniformOrbitOpen_boundary_lift f hL d V c k W a⟩

end OrbitBoundaryAtlas
end FLT.Mazur.HilbertChart.AffineRestriction
