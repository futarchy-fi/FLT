/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertOrbitBoundaryAtlasOriginalLift
public import FLT.Mazur.HilbertOrbitBoundaryFiniteDescent

/-!
# Recovering the original boundary section from finite chart descent

The descended function restricts to the original boundary section on its whole
orbit domain. A vanishing simultaneous obstruction therefore gives an original
invariant lift and its actual finite lifting-multiplier certificate.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve EquivalenceRelationNormalizedFrames
open RelativeRelationOrbit InvariantOpenRelationDiagram
open FiniteGroupRestriction SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] relativeFppfSheaf AmpleLineBundle
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

local notation "ec" => originalClosedEquivalence f hL d V c k
local notation "i" => originalBoundarySourceMap f hL d V c k
local notation "z" => originalClosedArrow f hL d V c k
local notation "hp" => originalClosedArrow_fst f hL d V c k
local notation "hq" => originalClosedArrow_snd f hL d V c k
local notation "m" => originalClosedInvariantMap f hL d V c k
local notation "Wc" => (TopologicalSpace.Opens.map (m).base).obj W
local notation "Ec" => (pullOpen ec Wc).val
local notation "g" => (openSourceMap e ec i z hp hq W).left
attribute [local irreducible] originalBoundarySource originalBoundarySourceMap
  originalClosedRelation originalClosedFst originalClosedSnd originalClosedArrow
  originalClosedEquivalence InvariantBoundary.boundary
attribute [local irreducible] RelativeRelationOrbit.openSourceMap
  InvariantOpenRelationDiagram.sourceMap InvariantOpenRelationDiagram.orbitFunctions

variable (t : (invariantSheaf (originalClosedEquivalence f hL d V c k)).obj.obj
  (op ((TopologicalSpace.Opens.map (originalClosedInvariantMap f hL d V c k).base).obj W)))

/-- Exact boundary agreement on one chart holds on every original-boundary test. -/
theorem boundary_chart_test (v : Sections f hL d V c k W hW) (a : C)
    (hv : normalizedBoundaryChartMap f hL d V c k a.val.size a.val.label a.val.domain a.val.stable
      (v a) = normalizedOrbitBoundaryCoefficient f hL d V c k a.val.size a.val.label W
        a.val.domain a.val.stable a.val.overDomain t)
    {T : Scheme.{0}} (u : T ⟶ a.val.domain.toScheme) (w : T ⟶ (Ec).toScheme)
    (hu : u ≫ chartMap f hL d V c k W a.val = w ≫ g) :
    u.appTop (v a).val = w.appTop (orbitFunctions ec Wc t).val := by
  have hw : u ≫ a.val.domain.ι ≫ first (Over.Hom.left (AffineRestriction.fst f hL d V c k))
      (Over.Hom.left (AffineRestriction.snd f hL d V c k)) (Fin a.val.size) a.val.label =
        w ≫ (Ec).ι ≫ (i).left := by
    have hc := congrArg (fun φ ↦ φ ≫ (E).ι) hu
    simpa only [Category.assoc, chartMap_inclusion, boundaryMap_inclusion,
      normalizedFullRelationFirst] using hc
  apply InvariantBoundary.boundary_coefficient_test a.val.label (i).left a.val.domain Ec u w hw
    (normalizedOrbitBoundary_domain_le f hL d V c k a.val.size a.val.label W a.val.domain
      a.val.overDomain)
    (v a).val (orbitFunctions ec Wc t).val
  simpa only [normalizedBoundaryChartMap, invariantMap_val,
    normalizedOrbitBoundaryCoefficient_val, normalizedOriginalBoundaryInclusion,
    normalizedOriginalBoundaryEndpoint] using congrArg Subtype.val hv

/-- Atlas boundary equalities recover the whole unchanged original boundary function. -/
theorem descended_section_boundary (v : Sections f hL d V c k W hW)
    (hv : ∀ a : C, normalizedBoundaryChartMap f hL d V c k a.val.size a.val.label a.val.domain
      a.val.stable
      (v a) = normalizedOrbitBoundaryCoefficient f hL d V c k a.val.size a.val.label W
        a.val.domain a.val.stable a.val.overDomain t)
    (s : Γ((E).toScheme, ⊤))
    (hs : ∀ a : C, (chartMap f hL d V c k W a.val).appTop s = (v a).val) :
    (g).appTop s = (orbitFunctions ec Wc t).val := by
  exact SchemeFppfFamily.boundary_eq_of_chart_tests (finiteFppfCover f hL d V c k W hW)
    g s (orbitFunctions ec Wc t).val (fun T a u w hu ↦
      (congrArg (fun x ↦ u.appTop x) (hs a)).trans
        (boundary_chart_test f hL d V c k W hW t v a (hv a) u w hu))

/-- Transport a descended equalized source function back to its actual chart values. -/
theorem original_section_of_equalized (v : ∀ j : C, Γ(j.val.domain.toScheme, ⊤))
    (s : Γ((E).toScheme, ⊤))
    (hs : ∀ j : C, (chartMap f hL d V c k W j.val).appTop s = v j)
    (he : (Over.Hom.left (AffineRestriction.fst f hL d V c k) ∣_ E).appTop s =
      ((Over.Hom.left (AffineRestriction.snd f hL d V c k)).resLE E _
        (pullOpen_preimage_eq e W).le).appTop s) :
    ∃ a : (invariantSheaf e).obj.obj (op W), ∀ j : C,
      (chartMap f hL d V c k W j.val).appTop (orbitFunctions e W a).val = v j := by
  obtain ⟨a, ha⟩ := source_invariant_exists f hL d V c k W s he
  exact ⟨a, fun j ↦ (congrArg (fun coeff ↦ (chartMap f hL d V c k W j.val).appTop coeff) ha).trans
    (hs j)⟩

/-- A compatible finite chart family is the pullback of an actual original invariant section. -/
theorem original_section_of_compatible (v : ∀ j : C, Γ(j.val.domain.toScheme, ⊤))
    (hv : ∀ a b : C,
      (MixedFrames.mixedChartFirst a.val.label b.val.label a.val.domain b.val.domain).appTop
        (v a) =
      (MixedFrames.mixedChartSecond a.val.label b.val.label a.val.domain b.val.domain).appTop
        (v b)) :
    ∃ a : (invariantSheaf e).obj.obj (op W), ∀ j : C,
      (chartMap f hL d V c k W j.val).appTop (orbitFunctions e W a).val = v j := by
  obtain ⟨s, hs, _⟩ := compatible_sections_descend f hL d V c k W hW
    v hv
  exact original_section_of_equalized f hL d V c k W hW v s hs
    (descended_section_equalized f hL d V c k W hW v hv s hs)

/-- A solved finite correction problem yields an actual lift in the original invariant sheaf. -/
theorem original_lift_of_obstruction_zero (ht : obstruction f hL d V c k W hW t = 0) :
    ∃ a : (invariantSheaf e).obj.obj (op W), (m).c.app (op W) a = t := by
  obtain ⟨v, hv, hc⟩ := (obstruction_eq_zero_iff f hL d V c k W hW t).mp ht
  obtain ⟨a, ha⟩ := original_section_of_compatible f hL d V c k W hW (fun j ↦ (v j).val) hc
  have hn : (orbitFunctions ec Wc ((m).c.app (op W) a)).val =
      (g).appTop (orbitFunctions e W a).val :=
    (congrArg Subtype.val (openFunctionMap_natural e ec i z hp hq W a)).symm
  have hb := descended_section_boundary f hL d V c k W hW t v hv
    (orbitFunctions e W a).val ha
  exact ⟨a, (orbitFunctions ec Wc).injective (Subtype.ext (hn.trans hb))⟩

/-- Solved corrections give the actual finite certificate on the unchanged closed source. -/
theorem original_certificate_of_obstruction_zero
    (ht : obstruction f hL d V c k W hW t = 0) :
    ∃ a : originalBoundaryLiftIdeal f hL d V c k W t →₀
        (sourceSheaf ec).obj.obj (op Wc),
      a.sum (fun v b ↦ b * (invariantInclusion ec).hom.app (op Wc)
        ((m).c.app (op W) v.val)) = 1 := by
  apply (mem_originalBoundaryCertifiedSections_iff f hL d V c k W t).mp
  obtain ⟨a, ha⟩ := original_lift_of_obstruction_zero f hL d V c k W hW t ht
  rw [← ha]
  exact image_mem_sourceCertifiedSections _ _ a

/-- On an affine source domain, solved corrections cover the whole original boundary. -/
theorem original_boundary_cover_of_obstruction_zero
    (ht : obstruction f hL d V c k W hW t = 0) :
    (TopologicalSpace.Opens.map (m).base).obj
      (originalBoundaryLiftOpen f hL d V c k W t) = Wc :=
  (originalBoundaryLift_boundary_cover_iff_certificate f hL d V c k W t hW).mpr
    (original_certificate_of_obstruction_zero f hL d V c k W hW t ht)

end OrbitBoundaryAtlas.FiniteAtlas
end FLT.Mazur.HilbertChart.AffineRestriction
