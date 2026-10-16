/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertOrbitBoundaryAtlasLifts
public import FLT.Mazur.SchemeFppfFamilyFunctionDescent
public import FLT.Mazur.EquivalenceRelationMixedChartTests

/-!
# Descent from compatible exhaustive normalized chart functions

Full mixed relation compatibility gives actual descent to the original source
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
namespace OrbitBoundaryAtlas
local notation "e" => equivalence f hL d V c k
variable (W : TopologicalSpace.Opens (Orbit (equivalence f hL d V c k)))
set_option quotPrecheck false
local notation "E" => (pullOpen e W).val

local notation "C" => Chart f hL d V c k W

/-- Full mixed equations descend to one unique function on the original source domain. -/
theorem compatible_sections_descend (v : ∀ a : C, Γ(a.domain.toScheme, ⊤))
    (hv : ∀ a b : C,
      (MixedFrames.mixedChartFirst a.label b.label a.domain b.domain).appTop (v a) =
        (MixedFrames.mixedChartSecond a.label b.label a.domain b.domain).appTop (v b)) :
    ∃! s : Γ((E).toScheme, ⊤), ∀ a : C,
      (chartMap f hL d V c k W a).appTop s = v a := by
  apply SchemeFppfFamily.family_sections_existsUnique (fppfCover f hL d V c k W) v
  intro T a b g h hh
  change g ≫ chartMap f hL d V c k W a = h ≫ chartMap f hL d V c k W b at hh
  apply MixedFrames.mixedChart_compatible_same_endpoint a.label b.label a.domain b.domain
    g h (fullRelationSchemeEquivalence f hL d V c k) _ (v a) (v b) (hv a b)
  have he := congrArg (fun z ↦ z ≫ (E).ι) hh
  simpa only [Category.assoc, chartMap_inclusion,
    normalizedFullRelationFirst] using he

local notation "p" => Over.Hom.left (AffineRestriction.fst f hL d V c k)
local notation "q" => Over.Hom.left (AffineRestriction.snd f hL d V c k)
local notation "pW" => (p) ∣_ E
local notation "qW" => (q).resLE E _ (pullOpen_preimage_eq e W).le

/-- The descended function satisfies the entire original relation, including nilpotent tests. -/
theorem descended_section_equalized (v : ∀ a : C, Γ(a.domain.toScheme, ⊤))
    (hv : ∀ a b : C,
      (MixedFrames.mixedChartFirst a.label b.label a.domain b.domain).appTop (v a) =
        (MixedFrames.mixedChartSecond a.label b.label a.domain b.domain).appTop (v b))
    (s : Γ((E).toScheme, ⊤))
    (hs : ∀ a : C, (chartMap f hL d V c k W a).appTop s = v a) :
    (pW).appTop s = (qW).appTop s := by
  apply SchemeFppfFamily.relation_eq_of_chart_tests (fppfCover f hL d V c k W) pW qW s
  intro T a b g h w hp hq
  change w ≫ pW = g ≫ chartMap f hL d V c k W a at hp
  change w ≫ qW = h ≫ chartMap f hL d V c k W b at hq
  change g.appTop ((chartMap f hL d V c k W a).appTop s) =
    h.appTop ((chartMap f hL d V c k W b).appTop s)
  rw [hs a, hs b]
  apply MixedFrames.mixedChart_compatible_test a.label b.label a.domain b.domain
    g h (w ≫ ((p) ⁻¹ᵁ E).ι) _ _ (v a) (v b) (hv a b)
  · have he := congrArg (fun z ↦ z ≫ (E).ι) hp
    simpa only [Category.assoc, morphismRestrict_ι, chartMap_inclusion,
    normalizedFullRelationFirst] using he
  · have he := congrArg (fun z ↦ z ≫ (E).ι) hq
    simpa only [Category.assoc, Scheme.Hom.resLE_comp_ι, chartMap_inclusion,
    normalizedFullRelationFirst] using he

local notation "ec" => originalClosedEquivalence f hL d V c k
local notation "m" => originalClosedInvariantMap f hL d V c k
local notation "Wc" => (TopologicalSpace.Opens.map (m).base).obj W
variable (t : (invariantSheaf (originalClosedEquivalence f hL d V c k)).obj.obj
  (op ((TopologicalSpace.Opens.map (originalClosedInvariantMap f hL d V c k).base).obj W)))

/-- A solved simultaneous correction problem produces an actual original-source function. -/
theorem source_lift_of_obstruction_zero (ht : obstruction f hL d V c k W t = 0) :
    ∃ (v : Sections f hL d V c k W) (s : Γ((E).toScheme, ⊤)),
      (pW).appTop s = (qW).appTop s ∧
      (∀ a : C, (chartMap f hL d V c k W a).appTop s = (v a).val) ∧
      (∀ a : C, normalizedBoundaryChartMap f hL d V c k a.size a.label a.domain a.stable
        (v a) = normalizedOrbitBoundaryCoefficient f hL d V c k a.size a.label W
          a.domain a.stable a.overDomain t) ∧
      ∀ a b : C, (MixedFrames.mixedChartFirst a.label b.label a.domain b.domain).appTop
        (v a).val = (MixedFrames.mixedChartSecond a.label b.label a.domain b.domain).appTop
          (v b).val := by
  obtain ⟨v, hv, hc⟩ := (obstruction_eq_zero_iff f hL d V c k W t).mp ht
  obtain ⟨s, hs, _⟩ := compatible_sections_descend f hL d V c k W (fun a ↦ (v a).val) hc
  exact ⟨v, s, descended_section_equalized f hL d V c k W (fun a ↦ (v a).val) hc s hs,
    hs, hv, hc⟩

end OrbitBoundaryAtlas
end FLT.Mazur.HilbertChart.AffineRestriction
