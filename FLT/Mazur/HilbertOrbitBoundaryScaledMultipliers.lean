/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertOrbitBoundaryFiniteScalars

/-!
# Exact scalar boundary naturality and scaled original multipliers

The constructed scalar family restricts to the original scalar on the exact
closed boundary. Compatible numerators with power-scaled boundary values
therefore give multipliers in the original lifting ideal.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve EquivalenceRelationNormalizedFrames
open RelativeRelationOrbit InvariantOpenRelationDiagram
open FiniteGroupRestriction SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] SchemeFunctionGroundChange.sectionAlgebra
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

local notation "φ" => originalClosedSectionPullback f hL d V c k W
attribute [local irreducible] scalarFamily normalizedBoundaryChartMap
  normalizedOrbitBoundaryCoefficient

/-- The chart boundary square commutes on the unchanged original orbit domains. -/
theorem scalar_chart_boundary_square (j : C) :
    ((normalizedOriginalBoundaryEndpoint f hL d V c k j.val.size j.val.label).resLE Ec
      (normalizedOriginalBoundaryInclusion f hL d V c k j.val.size j.val.label ⁻¹ᵁ j.val.domain)
      (normalizedOrbitBoundary_domain_le f hL d V c k j.val.size j.val.label W j.val.domain
        j.val.overDomain)) ≫ g =
      (normalizedOriginalBoundaryInclusion f hL d V c k j.val.size j.val.label ∣_ j.val.domain) ≫
        chartMap f hL d V c k W j.val := by
  apply (cancel_mono (E).ι).mp
  simp only [Category.assoc, boundaryMap_inclusion, chartMap_inclusion,
    Scheme.Hom.resLE_comp_ι_assoc, morphismRestrict_ι_assoc]
  exact congrArg (fun morphism ↦
    (normalizedOriginalBoundaryInclusion f hL d V c k j.val.size j.val.label ⁻¹ᵁ
      j.val.domain).ι ≫ morphism)
    (InvariantBoundary.endpoint_condition (p := Over.Hom.left (AffineRestriction.fst f hL d V c k))
      (q := Over.Hom.left (AffineRestriction.snd f hL d V c k))
      (Fin j.val.size) j.val.label (i).left).symm

/-- Constructed scalar coefficients restrict to the actual original boundary scalar. -/
theorem scalarFamily_boundary (a : (invariantSheaf e).obj.obj (op W)) (j : C) :
    normalizedBoundaryChartMap f hL d V c k j.val.size j.val.label j.val.domain j.val.stable
      (scalarFamily f hL d V c k W hW a j) =
        normalizedOrbitBoundaryCoefficient f hL d V c k j.val.size j.val.label W j.val.domain
          j.val.stable j.val.overDomain (φ a) := by
  apply Subtype.ext
  have hn : (orbitFunctions ec Wc (φ a)).val = (g).appTop (orbitFunctions e W a).val :=
    (congrArg Subtype.val (openFunctionMap_natural e ec i z hp hq W a)).symm
  let endpoint :=
    (normalizedOriginalBoundaryEndpoint f hL d V c k j.val.size j.val.label).resLE Ec
      (normalizedOriginalBoundaryInclusion f hL d V c k j.val.size j.val.label ⁻¹ᵁ j.val.domain)
      (normalizedOrbitBoundary_domain_le f hL d V c k j.val.size j.val.label W j.val.domain
        j.val.overDomain)
  have he := congrArg (fun morphism ↦ morphism.appTop (orbitFunctions e W a).val)
    (scalar_chart_boundary_square f hL d V c k W hW j)
  have hn' := congrArg (fun coeff : Γ((Ec).toScheme, ⊤) ↦ endpoint.appTop coeff) hn
  have hfinal := he.symm.trans hn'.symm
  simp only [normalizedBoundaryChartMap, invariantMap_val, scalarFamily_val,
    normalizedOrbitBoundaryCoefficient_val, Scheme.Hom.comp_appTop,
    ConcreteCategory.comp_apply, CommRingCat.Hom.hom, endpoint] at hfinal ⊢
  convert! hfinal using 1

/-- Original boundary multiplication is retained in every exact chart coefficient. -/
theorem boundaryCoefficient_power_mul
    (s : (invariantSheaf ec).obj.obj (op Wc)) (N : ℕ) (j : C) :
    normalizedOrbitBoundaryCoefficient f hL d V c k j.val.size j.val.label W j.val.domain
      j.val.stable j.val.overDomain (s ^ N * t) =
    normalizedOrbitBoundaryCoefficient f hL d V c k j.val.size j.val.label W j.val.domain
      j.val.stable j.val.overDomain s ^ N *
    normalizedOrbitBoundaryCoefficient f hL d V c k j.val.size j.val.label W j.val.domain
      j.val.stable j.val.overDomain t := by
  apply Subtype.ext
  change (normalizedOrbitBoundaryCoefficient f hL d V c k j.val.size j.val.label W
    j.val.domain j.val.stable j.val.overDomain (s ^ N * t)).val =
      (normalizedOrbitBoundaryCoefficient f hL d V c k j.val.size j.val.label W
        j.val.domain j.val.stable j.val.overDomain s).val ^ N *
      (normalizedOrbitBoundaryCoefficient f hL d V c k j.val.size j.val.label W
        j.val.domain j.val.stable j.val.overDomain t).val
  simp only [normalizedOrbitBoundaryCoefficient_val]
  let sourceMap : (invariantSheaf ec).obj.obj (op Wc) →+* Γ((Ec).toScheme, ⊤) :=
    { toFun := fun x ↦ (orbitFunctions ec Wc x).val
      map_zero' := congrArg Subtype.val (map_zero (orbitFunctions ec Wc))
      map_one' := congrArg Subtype.val (map_one (orbitFunctions ec Wc))
      map_add' := fun x y ↦ congrArg Subtype.val (map_add (orbitFunctions ec Wc) x y)
      map_mul' := fun x y ↦ congrArg Subtype.val (map_mul (orbitFunctions ec Wc) x y) }
  let coeffMap :=
    ((normalizedOriginalBoundaryEndpoint f hL d V c k j.val.size j.val.label).resLE Ec
      (normalizedOriginalBoundaryInclusion f hL d V c k j.val.size j.val.label ⁻¹ᵁ j.val.domain)
      (normalizedOrbitBoundary_domain_le f hL d V c k j.val.size j.val.label W j.val.domain
        j.val.overDomain)).appTop.hom.comp
      sourceMap
  change coeffMap (s ^ N * t) = coeffMap s ^ N * coeffMap t
  rw [map_mul, map_pow]

/-- Compatible power-scaled chart boundary lifts yield the specified original multiplier. -/
theorem original_power_mem_of_scaled_boundary (a : (invariantSheaf e).obj.obj (op W))
    (N : ℕ) (w : Sections f hL d V c k W hW)
    (hb : ∀ j : C,
      normalizedBoundaryChartMap f hL d V c k j.val.size j.val.label j.val.domain j.val.stable
        (w j) =
      normalizedBoundaryChartMap f hL d V c k j.val.size j.val.label j.val.domain j.val.stable
        (scalarFamily f hL d V c k W hW a j) ^ N *
      normalizedOrbitBoundaryCoefficient f hL d V c k j.val.size j.val.label W j.val.domain
        j.val.stable j.val.overDomain t)
    (hc : ∀ j l : C,
      (MixedFrames.mixedChartFirst j.val.label l.val.label j.val.domain l.val.domain).appTop
        (w j).val =
      (MixedFrames.mixedChartSecond j.val.label l.val.label j.val.domain l.val.domain).appTop
        (w l).val) : a ^ N ∈ originalBoundaryLiftIdeal f hL d V c k W t := by
  obtain ⟨b, hbb⟩ := original_section_of_compatible f hL d V c k W hW (fun j ↦ (w j).val) hc
  have hw (j : C) :
      normalizedBoundaryChartMap f hL d V c k j.val.size j.val.label j.val.domain j.val.stable
        (w j) =
      normalizedOrbitBoundaryCoefficient f hL d V c k j.val.size j.val.label W j.val.domain
        j.val.stable j.val.overDomain ((φ a) ^ N * t) := by
    exact (hb j).trans ((congrArg (fun coeff ↦ coeff ^ N *
      normalizedOrbitBoundaryCoefficient f hL d V c k j.val.size j.val.label W j.val.domain
        j.val.stable j.val.overDomain t)
      (scalarFamily_boundary f hL d V c k W hW a j)).trans
        (boundaryCoefficient_power_mul f hL d V c k W hW t (φ a) N j).symm)
  have hboundary := descended_section_boundary f hL d V c k W hW ((φ a) ^ N * t)
    w hw (orbitFunctions e W b).val hbb
  change ∃ b, φ b = φ (a ^ N) * t
  refine ⟨b, ?_⟩
  rw [map_pow]
  exact original_boundary_power f hL d V c k W t a b N hboundary

end OrbitBoundaryAtlas.FiniteAtlas
end FLT.Mazur.HilbertChart.AffineRestriction
