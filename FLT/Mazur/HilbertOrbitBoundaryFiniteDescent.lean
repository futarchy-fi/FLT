/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertOrbitBoundaryFiniteLifts
public import FLT.Mazur.SchemeFppfFamilyFunctionDescent
public import FLT.Mazur.EquivalenceRelationMixedChartTests

/-!
# Descent from compatible finite normalized chart functions

Full mixed relation compatibility on the finite covering atlas gives actual descent to the original
  source
orbit domain. The descent is unique and recovers every chart coefficient.
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
namespace OrbitBoundaryAtlas.FiniteAtlas
attribute [local irreducible] finiteCharts lifts obstruction
local notation "e" => equivalence f hL d V c k
variable (W : TopologicalSpace.Opens (Orbit (equivalence f hL d V c k)))
set_option quotPrecheck false
local notation "E" => (pullOpen e W).val

variable (hW : IsAffineOpen (pullOpen (equivalence f hL d V c k) W).val)
local notation "C" => finiteCharts f hL d V c k W hW

/-- Full mixed equations descend to one unique function on the original source domain. -/
theorem compatible_sections_descend (v : ∀ a : C, Γ(a.val.domain.toScheme, ⊤))
    (hv : ∀ a b : C,
      (MixedFrames.mixedChartFirst a.val.label b.val.label a.val.domain b.val.domain).appTop (v a) =
        (MixedFrames.mixedChartSecond a.val.label b.val.label a.val.domain b.val.domain).appTop (v
          b)) :
    ∃! s : Γ((E).toScheme, ⊤), ∀ a : C,
      (chartMap f hL d V c k W a.val).appTop s = v a := by
  apply SchemeFppfFamily.family_sections_existsUnique (finiteFppfCover f hL d V c k W hW) v
  intro T a b g h hh
  change g ≫ chartMap f hL d V c k W a.val = h ≫ chartMap f hL d V c k W b.val at hh
  apply MixedFrames.mixedChart_compatible_same_endpoint a.val.label b.val.label a.val.domain
    b.val.domain
    g h (fullRelationSchemeEquivalence f hL d V c k) _ (v a) (v b) (hv a b)
  have he := congrArg (fun z ↦ z ≫ (E).ι) hh
  simpa only [Category.assoc, chartMap_inclusion,
    normalizedFullRelationFirst] using he

local notation "p" => Over.Hom.left (AffineRestriction.fst f hL d V c k)
local notation "q" => Over.Hom.left (AffineRestriction.snd f hL d V c k)
local notation "pW" => (p) ∣_ E
local notation "qW" => (q).resLE E _ (pullOpen_preimage_eq e W).le

/-- The descended function satisfies the entire original relation, including nilpotent tests. -/
theorem descended_section_equalized (v : ∀ a : C, Γ(a.val.domain.toScheme, ⊤))
    (hv : ∀ a b : C,
      (MixedFrames.mixedChartFirst a.val.label b.val.label a.val.domain b.val.domain).appTop (v a) =
        (MixedFrames.mixedChartSecond a.val.label b.val.label a.val.domain b.val.domain).appTop (v
          b))
    (s : Γ((E).toScheme, ⊤))
    (hs : ∀ a : C, (chartMap f hL d V c k W a.val).appTop s = v a) :
    (pW).appTop s = (qW).appTop s := by
  apply SchemeFppfFamily.relation_eq_of_chart_tests (finiteFppfCover f hL d V c k W hW) pW qW s
  intro T a b g h w hp hq
  change w ≫ pW = g ≫ chartMap f hL d V c k W a.val at hp
  change w ≫ qW = h ≫ chartMap f hL d V c k W b.val at hq
  change g.appTop ((chartMap f hL d V c k W a.val).appTop s) =
    h.appTop ((chartMap f hL d V c k W b.val).appTop s)
  rw [hs a, hs b]
  apply MixedFrames.mixedChart_compatible_test a.val.label b.val.label a.val.domain b.val.domain
    g h (w ≫ ((p) ⁻¹ᵁ E).ι) _ _ (v a) (v b) (hv a b)
  · have he := congrArg (fun z ↦ z ≫ (E).ι) hp
    simpa only [Category.assoc, morphismRestrict_ι, chartMap_inclusion,
    normalizedFullRelationFirst] using he
  · have he := congrArg (fun z ↦ z ≫ (E).ι) hq
    simpa only [Category.assoc, Scheme.Hom.resLE_comp_ι, chartMap_inclusion,
    normalizedFullRelationFirst] using he

end OrbitBoundaryAtlas.FiniteAtlas
end FLT.Mazur.HilbertChart.AffineRestriction
