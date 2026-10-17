/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertUniformOriginalLiftingOpen
public import FLT.Mazur.HilbertCompleteInteriorCharts
public import FLT.Mazur.EquivalenceRelationFiniteCompleteInterior

/-!
# Actual uniform lifting coverage on the original finite relation locus

Complete lifts over finite original relation neighborhoods are interior
complete. Stable affine refinement puts their points in the constructed
uniform source opens, so the original orbit image of the finite relation
locus is covered. No claim that every boundary point meets this locus is made.
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

/-- A finite neighborhood of the original first projection gives actual uniform coverage. -/
theorem projection_mem_uniformLiftingOpen_of_finiteTarget (x : A.left)
    (hx : projection eo x ∈ W) (hf : x ∈ SchemeOpenEnvelope.finiteTargetOpen p) :
    projection eo x ∈ uniformLiftingOpen f hL d V c k W := by
  let _ := selectedHilbertSource_isLocallyNoetherian f d V k
  obtain ⟨n, o, y, hy, hc⟩ := exists_complete_interior_lift_of_finiteTarget e x hf
  have hyW : normalizedFullRelationFirst f hL d V c k n o y ∈ (pullOpen eo W).val := by
    change first p q (Fin n) o y ∈ (pullOpen eo W).val
    rw [hy]
    exact hx
  obtain ⟨U, hU, hUW, ha, hyU, _, _⟩ :=
    exists_completeInterior_orbit_chart f hL d V c k W n o y hyW hc
  let a : Charts := ⟨n, o, U, ha, hU, hUW⟩
  have huni : (⟨y, hyU⟩ : U.toScheme) ∈ uniformSourceOpen e (Fin n) o U hU :=
    completeInterior_le_uniformSourceOpen e (Fin n) o U hU hc
  apply (mem_uniformLiftingOpen f hL d V c k W (projection eo x)).mpr
  refine ⟨a, ?_⟩
  unfold uniformOrbitOpen orbitImageOpen etaleSourceImage
  change projection eo x ∈ projection eo '' Set.range _
  refine ⟨x, ⟨⟨⟨y, hyU⟩, huni⟩, ?_⟩, rfl⟩
  exact hy

/-- The actual original orbit region reached through finite relation neighborhoods. -/
def finiteRelationOrbitOpen : TopologicalSpace.Opens (Orbit eo) :=
  orbitImageOpen eo (q).isOpenMap
    (SchemeOpenEnvelope.finiteTargetOpen p ⊓ (pullOpen eo W).val)

/-- The constructed finite relation region is contained in the original uniform lifting domain. -/
theorem finiteRelationOrbitOpen_le_uniformLiftingOpen :
    finiteRelationOrbitOpen f hL d V c k W ≤ uniformLiftingOpen f hL d V c k W := by
  unfold finiteRelationOrbitOpen orbitImageOpen
  rintro _ ⟨x, hx, rfl⟩
  exact projection_mem_uniformLiftingOpen_of_finiteTarget f hL d V c k W x hx.2 hx.1

/-- A finite original first projection removes the uniform coverage obstruction entirely. -/
theorem uniformLiftingOpen_eq_of_finite [IsFinite p] :
    uniformLiftingOpen f hL d V c k W = W := by
  apply le_antisymm (uniformLiftingOpen_le f hL d V c k W)
  intro x hx
  obtain ⟨y, rfl⟩ := projection_surjective eo x
  apply projection_mem_uniformLiftingOpen_of_finiteTarget f hL d V c k W y hx
  rw [SchemeOpenEnvelope.finiteTargetOpen_eq_top]
  trivial

end OrbitBoundaryAtlas
end FLT.Mazur.HilbertChart.AffineRestriction
