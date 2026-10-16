/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertNormalizedOrbitBoundaryCharts
public import FLT.Mazur.EquivalenceRelationNormalizedFrameCover
public import FLT.Mazur.SchemeFppfCoverInvariantFunctions

/-!
# An exhaustive affine atlas over each original Hilbert orbit domain

All stable affine normalized charts inside the original domain form an actual
etale and fppf covering family of its source. Sizes and labels vary independently.
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
attribute [local irreducible] relation fst snd equivalence
  EquivalenceRelationNormalizedFrames.source
namespace OrbitBoundaryAtlas
local notation "e" => equivalence f hL d V c k
variable (W : TopologicalSpace.Opens (Orbit (equivalence f hL d V c k)))
set_option quotPrecheck false
local notation "E" => (pullOpen e W).val

/-- Actual stable affine chart data lying over the specified original source domain. -/
structure Chart where
  /-- The number of independently chosen frame labels. -/
  size : ℕ
  /-- The label used for the first original endpoint. -/
  label : Fin size
  /-- The whole stable affine source open of this chart. -/
  domain : (normalizedFullRelationFrames f hL d V c k size label).Opens
  affine : IsAffineOpen domain
  stable : ∀ σ, (normalizedFullRelationAction f hL d V c k size label σ).hom ⁻¹ᵁ
    domain = domain
  overDomain : domain ≤ normalizedFullRelationFirst f hL d V c k size label ⁻¹ᵁ E

/-- The actual chart morphism to the unchanged source orbit domain. -/
def chartMap (a : Chart f hL d V c k W) : a.domain.toScheme ⟶ (E).toScheme :=
  (normalizedFullRelationFirst f hL d V c k a.size a.label).resLE E _ a.overDomain

instance chartMap_etale (a : Chart f hL d V c k W) :
    Etale (chartMap f hL d V c k W a) := by
  unfold chartMap
  infer_instance

omit [Etale V.hom] in
/-- The chart map is the original endpoint restricted to its actual open domain. -/
@[reassoc] theorem chartMap_inclusion (a : Chart f hL d V c k W) :
    chartMap f hL d V c k W a ≫ (E).ι =
      a.domain.ι ≫ normalizedFullRelationFirst f hL d V c k a.size a.label :=
  Scheme.Hom.resLE_comp_ι _ _

/-- Every original source point has an actual affine chart in this family. -/
theorem charts_cover (x : (E).toScheme) :
    ∃ (a : Chart f hL d V c k W) (y : a.domain.toScheme),
      chartMap f hL d V c k W a y = x := by
  obtain ⟨⟨n, o⟩, y, hy⟩ := normalizedFrames_covers
    (fullRelationSchemeEquivalence f hL d V c k) x.val
  change normalizedFullRelationFirst f hL d V c k n o y = x.val at hy
  have hyE : normalizedFullRelationFirst f hL d V c k n o y ∈ E := by
    rw [hy]
    exact x.property
  obtain ⟨U, ha, hyU, hUE, hU, _⟩ := exists_normalized_affine_original_domain
    f hL d V c k n o E (pullOpen_preimage_eq e W) y hyE
  let a : Chart f hL d V c k W := ⟨n, o, U, ha, hU, hUE⟩
  refine ⟨a, ⟨y, hyU⟩, ?_⟩
  apply Subtype.ext
  exact (Scheme.Hom.coe_resLE_apply _ _ _).trans hy

/-- The exhaustive atlas as an etale covering family. -/
def etaleCover : (E).toScheme.Cover (Scheme.precoverage @Etale) :=
  Scheme.Cover.mkOfCovers (Chart f hL d V c k W)
    (fun a ↦ a.domain.toScheme) (chartMap f hL d V c k W)
    (charts_cover f hL d V c k W) (fun _ ↦ inferInstance)

/-- The same exhaustive family as an fppf cover, suitable for coefficient descent. -/
def fppfCover : (E).toScheme.Cover Scheme.fppfPrecoverage :=
  Scheme.Cover.mkOfCovers (P := @Flat ⊓ @LocallyOfFinitePresentation)
    (Chart f hL d V c k W) (fun a ↦ a.domain.toScheme)
    (chartMap f hL d V c k W) (charts_cover f hL d V c k W)
    (fun _ ↦ ⟨inferInstance, inferInstance⟩)

/-- All atlas coefficients together detect equality on the original source. -/
theorem sections_ext {s t : Γ((E).toScheme, ⊤)}
    (h : ∀ a, (chartMap f hL d V c k W a).appTop s =
      (chartMap f hL d V c k W a).appTop t) : s = t :=
  SchemeFppfFamily.cover_sections_ext (fppfCover f hL d V c k W) h

end OrbitBoundaryAtlas
end FLT.Mazur.HilbertChart.AffineRestriction
