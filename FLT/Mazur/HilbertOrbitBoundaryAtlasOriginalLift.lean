/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertOrbitBoundaryAtlasDescent
public import FLT.Mazur.EquivalenceRelationBoundaryChartTests
public import FLT.Mazur.RelativeRelationOpenFunctionMap
public import FLT.Mazur.HilbertBoundaryCertifiedAlgebra

/-!
# Recovering the original boundary section from exhaustive chart descent

The descended function restricts to the original boundary section on its whole
orbit domain. A vanishing simultaneous obstruction therefore gives an original
invariant lift and its actual finite lifting-multiplier certificate.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.SchemeFppfFamily
/-- Boundary functions can be compared on all source-chart tests of the exact pullback. -/
theorem boundary_eq_of_chart_tests {X Y : Scheme.{0}}
    (C : Scheme.Cover.{0} Scheme.fppfPrecoverage X) (g : Y ⟶ X) (s : Γ(X, ⊤)) (t : Γ(Y, ⊤))
    (h : ∀ (T : Scheme.{0}) (a : C.I₀) (u : T ⟶ C.X a) (w : T ⟶ Y),
      u ≫ C.f a = w ≫ g → u.appTop ((C.f a).appTop s) = w.appTop t) :
    g.appTop s = t := by
  apply cover_sections_ext (C.pullback₁ g)
  intro a
  have he := h _ a (pullback.snd g (C.f a)) (pullback.fst g (C.f a))
    pullback.condition.symm
  simp only [← ConcreteCategory.comp_apply, ← Scheme.Hom.comp_appTop] at he ⊢
  exact (congrArg (fun z : pullback g (C.f a) ⟶ X ↦ z.appTop s)
    (pullback.condition (f := g) (g := C.f a))).trans he
end FLT.Mazur.SchemeFppfFamily

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
namespace OrbitBoundaryAtlas
local notation "e" => equivalence f hL d V c k
variable (W : TopologicalSpace.Opens (Orbit (equivalence f hL d V c k)))
set_option quotPrecheck false
local notation "E" => (pullOpen e W).val

local notation "C" => Chart f hL d V c k W

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
omit [IsAffine V.left] in
/-- The original open boundary map retains the unchanged closed inclusion. -/
@[reassoc] theorem boundaryMap_inclusion : (g) ≫ (E).ι = (Ec).ι ≫ (i).left :=
  Scheme.Hom.resLE_comp_ι _ _

attribute [local irreducible] RelativeRelationOrbit.openSourceMap
  InvariantOpenRelationDiagram.sourceMap InvariantOpenRelationDiagram.orbitFunctions

variable (t : (invariantSheaf (originalClosedEquivalence f hL d V c k)).obj.obj
  (op ((TopologicalSpace.Opens.map (originalClosedInvariantMap f hL d V c k).base).obj W)))

/-- Exact boundary agreement on one chart holds on every original-boundary test. -/
theorem boundary_chart_test (v : Sections f hL d V c k W) (a : C)
    (hv : normalizedBoundaryChartMap f hL d V c k a.size a.label a.domain a.stable
      (v a) = normalizedOrbitBoundaryCoefficient f hL d V c k a.size a.label W
        a.domain a.stable a.overDomain t)
    {T : Scheme.{0}} (u : T ⟶ a.domain.toScheme) (w : T ⟶ (Ec).toScheme)
    (hu : u ≫ chartMap f hL d V c k W a = w ≫ g) :
    u.appTop (v a).val = w.appTop (orbitFunctions ec Wc t).val := by
  have hw : u ≫ a.domain.ι ≫ first (Over.Hom.left (AffineRestriction.fst f hL d V c k))
      (Over.Hom.left (AffineRestriction.snd f hL d V c k)) (Fin a.size) a.label =
        w ≫ (Ec).ι ≫ (i).left := by
    have hc := congrArg (fun φ ↦ φ ≫ (E).ι) hu
    simpa only [Category.assoc, chartMap_inclusion, boundaryMap_inclusion,
      normalizedFullRelationFirst] using hc
  apply InvariantBoundary.boundary_coefficient_test a.label (i).left a.domain Ec u w hw
    (normalizedOrbitBoundary_domain_le f hL d V c k a.size a.label W a.domain a.overDomain)
    (v a).val (orbitFunctions ec Wc t).val
  simpa only [normalizedBoundaryChartMap, invariantMap_val,
    normalizedOrbitBoundaryCoefficient_val, normalizedOriginalBoundaryInclusion,
    normalizedOriginalBoundaryEndpoint] using congrArg Subtype.val hv

/-- Atlas boundary equalities recover the whole unchanged original boundary function. -/
theorem descended_section_boundary (v : Sections f hL d V c k W)
    (hv : ∀ a : C, normalizedBoundaryChartMap f hL d V c k a.size a.label a.domain a.stable
      (v a) = normalizedOrbitBoundaryCoefficient f hL d V c k a.size a.label W
        a.domain a.stable a.overDomain t)
    (s : Γ((E).toScheme, ⊤))
    (hs : ∀ a : C, (chartMap f hL d V c k W a).appTop s = (v a).val) :
    (g).appTop s = (orbitFunctions ec Wc t).val := by
  exact SchemeFppfFamily.boundary_eq_of_chart_tests (fppfCover f hL d V c k W)
    g s (orbitFunctions ec Wc t).val (fun T a u w hu ↦
      (congrArg (fun x ↦ u.appTop x) (hs a)).trans
        (boundary_chart_test f hL d V c k W t v a (hv a) u w hu))

omit [IsAffine V.left] [Etale V.hom] [IsAffine A.left] [IsOpenImmersion k.left] in
/-- An equalized original-source function determines an actual original invariant section. -/
theorem source_invariant_exists (s : Γ((E).toScheme, ⊤))
    (he : (Over.Hom.left (AffineRestriction.fst f hL d V c k) ∣_ E).appTop s =
      ((Over.Hom.left (AffineRestriction.snd f hL d V c k)).resLE E _
        (pullOpen_preimage_eq e W).le).appTop s) :
    ∃ a : (invariantSheaf e).obj.obj (op W), (orbitFunctions e W a).val = s := by
  let a : (invariantSheaf e).obj.obj (op W) := (orbitFunctions e W).symm ⟨s, by
    change ((Over.Hom.left (AffineRestriction.fst f hL d V c k)).resLE E _ le_rfl).appTop s =
      ((Over.Hom.left (AffineRestriction.snd f hL d V c k)).resLE E _
        (pullOpen_preimage_eq e W).le).appTop s
    simpa only [Scheme.Hom.resLE_eq_morphismRestrict] using he⟩
  exact ⟨a, congrArg Subtype.val ((orbitFunctions e W).apply_symm_apply _)⟩

/-- A solved exhaustive correction problem yields an actual lift in the original invariant sheaf. -/
theorem original_lift_of_obstruction_zero (ht : obstruction f hL d V c k W t = 0) :
    ∃ a : (invariantSheaf e).obj.obj (op W), (m).c.app (op W) a = t := by
  obtain ⟨v, s, he, hs, hv, _⟩ := source_lift_of_obstruction_zero f hL d V c k W t ht
  obtain ⟨a, ha⟩ := source_invariant_exists f hL d V c k W s he
  have hn : (orbitFunctions ec Wc ((m).c.app (op W) a)).val =
      (g).appTop (orbitFunctions e W a).val :=
    (congrArg Subtype.val (openFunctionMap_natural e ec i z hp hq W a)).symm
  have hb := descended_section_boundary f hL d V c k W t v hv s hs
  exact ⟨a, (orbitFunctions ec Wc).injective
    (Subtype.ext (hn.trans ((congrArg (fun x ↦ (g).appTop x) ha).trans hb)))⟩

/-- Solved corrections give the actual finite certificate on the unchanged closed source. -/
theorem original_certificate_of_obstruction_zero
    (ht : obstruction f hL d V c k W t = 0) :
    ∃ a : originalBoundaryLiftIdeal f hL d V c k W t →₀
        (sourceSheaf ec).obj.obj (op Wc),
      a.sum (fun v b ↦ b * (invariantInclusion ec).hom.app (op Wc)
        ((m).c.app (op W) v.val)) = 1 := by
  apply (mem_originalBoundaryCertifiedSections_iff f hL d V c k W t).mp
  obtain ⟨a, ha⟩ := original_lift_of_obstruction_zero f hL d V c k W t ht
  rw [← ha]
  exact image_mem_sourceCertifiedSections _ _ a

/-- On an affine source domain, solved corrections cover the whole original boundary. -/
theorem original_boundary_cover_of_obstruction_zero
    (ht : obstruction f hL d V c k W t = 0) (hW : IsAffineOpen E) :
    (TopologicalSpace.Opens.map (m).base).obj
      (originalBoundaryLiftOpen f hL d V c k W t) = Wc :=
  (originalBoundaryLift_boundary_cover_iff_certificate f hL d V c k W t hW).mpr
    (original_certificate_of_obstruction_zero f hL d V c k W t ht)

end OrbitBoundaryAtlas
end FLT.Mazur.HilbertChart.AffineRestriction
