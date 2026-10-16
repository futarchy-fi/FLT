/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertOrbitBoundaryAtlas
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# A finite affine atlas over a compact original orbit domain

Compactness selects finitely many actual stable normalized charts from the
exhaustive atlas. Their maps still form an etale and fppf cover of the entire
original domain, with independently varying frame sizes and labels.
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


/-- Affineness of the original source produces a finite set of actual covering charts. -/
theorem exists_finite_charts (hW : IsAffineOpen (pullOpen (equivalence f hL d V c k) W).val) :
    ∃ S : Finset (Chart f hL d V c k W),
    ∀ x : (E).toScheme, ∃ (a : Chart f hL d V c k W) (_ : a ∈ S)
      (y : a.domain.toScheme),
      chartMap f hL d V c k W a y = x := by
  classical
  let _ : IsAffine (E).toScheme := hW
  obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover
    (fun a : Chart f hL d V c k W ↦ Set.range (chartMap f hL d V c k W a))
    (fun a ↦ (chartMap f hL d V c k W a).isOpenMap.isOpen_range) (by
      intro x _
      obtain ⟨a, y, hy⟩ := charts_cover f hL d V c k W x
      exact Set.mem_iUnion.mpr ⟨a, y, hy⟩)
  refine ⟨S, fun x ↦ ?_⟩
  obtain ⟨a, ha⟩ := Set.mem_iUnion.mp (hS (Set.mem_univ x))
  obtain ⟨haS, y, hy⟩ := Set.mem_iUnion.mp ha
  exact ⟨a, haS, y, hy⟩

variable (hW : IsAffineOpen (pullOpen (equivalence f hL d V c k) W).val)

/-- The selected finite atlas consists of existing charts, with no new compatibility fields. -/
def finiteCharts : Finset (Chart f hL d V c k W) :=
  (exists_finite_charts f hL d V c k W hW).choose

/-- The selected chart maps actually cover the unchanged original source. -/
theorem finiteCharts_cover (x : (E).toScheme) :
    ∃ a : finiteCharts f hL d V c k W hW, ∃ y : a.val.domain.toScheme,
      chartMap f hL d V c k W a.val y = x := by
  obtain ⟨a, ha, y, hy⟩ := (exists_finite_charts f hL d V c k W hW).choose_spec x
  exact ⟨⟨a, ha⟩, y, hy⟩

/-- A finite etale covering family, using the actual selected chart maps. -/
def finiteEtaleCover : (E).toScheme.Cover (Scheme.precoverage @Etale) :=
  Scheme.Cover.mkOfCovers (finiteCharts f hL d V c k W hW)
    (fun a ↦ a.val.domain.toScheme) (fun a ↦ chartMap f hL d V c k W a.val)
    (finiteCharts_cover f hL d V c k W hW) (fun _ ↦ inferInstance)

/-- The finite atlas as an fppf family for exact coefficient descent. -/
def finiteFppfCover : (E).toScheme.Cover Scheme.fppfPrecoverage :=
  Scheme.Cover.mkOfCovers (P := @Flat ⊓ @LocallyOfFinitePresentation)
    (finiteCharts f hL d V c k W hW) (fun a ↦ a.val.domain.toScheme)
    (fun a ↦ chartMap f hL d V c k W a.val)
    (finiteCharts_cover f hL d V c k W hW) (fun _ ↦ ⟨inferInstance, inferInstance⟩)

instance finiteEtaleCoverFintype : Fintype (finiteEtaleCover f hL d V c k W hW).I₀ :=
  inferInstanceAs (Fintype (finiteCharts f hL d V c k W hW))

instance finiteFppfCoverFintype : Fintype (finiteFppfCover f hL d V c k W hW).I₀ :=
  inferInstanceAs (Fintype (finiteCharts f hL d V c k W hW))

/-- Finitely many chart coefficients detect equality on the whole original source. -/
theorem finite_sections_ext {s t : Γ((E).toScheme, ⊤)}
    (h : ∀ a : finiteCharts f hL d V c k W hW,
      (chartMap f hL d V c k W a.val).appTop s =
        (chartMap f hL d V c k W a.val).appTop t) : s = t :=
  SchemeFppfFamily.cover_sections_ext (finiteFppfCover f hL d V c k W hW) h

end OrbitBoundaryAtlas
end FLT.Mazur.HilbertChart.AffineRestriction
