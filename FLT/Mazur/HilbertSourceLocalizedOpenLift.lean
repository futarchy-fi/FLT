/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertSourceCompactRelation
public import FLT.Mazur.HilbertSubframeOriginalLocalization

/-!
# Exact localized original source lifts

The full source numerator gives an actual fraction whose localized boundary
is the prescribed unscaled coefficient. Its numerator solves the entire
original source relation; localization uses only original prime denominators.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve EquivalenceRelationNormalizedFrames
open RelativeRelationOrbit InvariantOpenRelationDiagram
open FiniteGroupRestriction SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] EquivalenceRelationNormalizedFrames.source
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
local notation "i" => Over.Hom.left (originalBoundarySourceMap f hL d V c k)
local notation "r" => Over.Hom.left (originalClosedFst f hL d V c k)
local notation "s" => Over.Hom.left (originalClosedSnd f hL d V c k)
local notation "z" => Over.Hom.left (originalClosedArrow f hL d V c k)
local notation "hr" => originalClosedFst_isPullback f hL d V c k
local notation "hs" => congrArg Over.Hom.left (originalClosedArrow_snd f hL d V c k)
local notation "m" => originalClosedInvariantMap f hL d V c k
attribute [local irreducible] originalBoundarySource originalBoundarySourceMap
  originalClosedRelation originalClosedFst originalClosedSnd originalClosedArrow
  originalClosedEquivalence relation AffineRestriction.fst AffineRestriction.snd equivalence
variable (n : ℕ) (o : Fin n)
local notation "N" => normalizedFullRelationFrames f hL d V c k n o
local notation "ρ" => normalizedOriginalBoundaryAction f hL d V c k n o
local notation "τ" => normalizedFullRelationAction f hL d V c k n o
local notation "j" => normalizedOriginalBoundaryInclusion f hL d V c k n o
local notation "b" => normalizedOriginalBoundaryEndpoint f hL d V c k n o
local notation "hj" => normalizedOriginalBoundaryAction_inclusion f hL d V c k n o
variable (W : TopologicalSpace.Opens (Orbit (equivalence f hL d V c k)))
set_option quotPrecheck false
local notation "Wc" => (TopologicalSpace.Opens.map (m).base).obj W
local notation "Uc" => (pullOpen ec Wc).val
variable (U : (normalizedFullRelationFrames f hL d V c k n o).Opens)
  (hU : ∀ σ : Equiv.Perm (Fin n),
    (normalizedFullRelationAction f hL d V c k n o σ).hom ⁻¹ᵁ U = U)
  (hUW : U ≤ normalizedFullRelationFirst f hL d V c k n o ⁻¹ᵁ
    (pullOpen (equivalence f hL d V c k) W).val)

local notation "Ω" => (invariantSheaf eo).obj.obj (op W)
local notation "Sinv" => invariantCoordinates (restrictedAction τ U hU)
local notation "E" => (pullOpen eo W).val

local notation "kS" => U.ι ≫ normalizedFullRelationFirst f hL d V c k n o
local notation "D" => SchemeRelationRestriction.doubleDomain p q kS
local notation "F" => SchemeRelationRestriction.fst p q kS
local notation "H" => SchemeRelationRestriction.snd p q kS
local notation "τU" => restrictedAction τ U hU
local notation "jU" => j ∣_ U
local notation "σ" => normalizedOriginalScalarMap f hL d V c k n o W U hU hUW
local notation "σ₀" => invariantScalarCoordinates τU σ
local notation "Tsource" => (sourceSheaf ec).obj.obj (op Wc)
local notation "κ" => ((invariantInclusion ec).hom.app (op Wc)).hom.comp
  (originalClosedSectionPullback f hL d V c k W)

attribute [local irreducible] normalizedOriginalScalarMap
  SchemeRelationRestriction.doubleDomain SchemeRelationRestriction.fst
  SchemeRelationRestriction.snd SchemeRelationRestriction.arrow

local notation "Bsource" => invariantCoordinates (boundaryOpenAction ρ τ j hj U hU)
local notation "α" => normalizedOriginalBoundaryHom f hL d V c k n o W U hU hUW
variable (ha : IsAffineOpen U) (O : U.toScheme.Opens)
  (hO : ∀ g : Equiv.Perm (Fin n),
    (restrictedAction (normalizedFullRelationAction f hL d V c k n o) U hU g).hom ⁻¹ᵁ O = O)
  (P : Ideal ((sourceSheaf (originalClosedEquivalence f hL d V c k)).obj.obj
    (op ((TopologicalSpace.Opens.map
      (originalClosedInvariantMap f hL d V c k).base).obj W)))) [P.IsPrime]
local notation "M" => originalSubframePrimeDenominators f hL d V c k W P

attribute [local irreducible] LocalizedModule.map normalizedOriginalBoundary
  normalizedOriginalBoundaryInclusion normalizedOriginalBoundaryAction
  normalizedFullRelationFrames normalizedFullRelationAction

/-- The actual boundary map after localization at the original boundary prime. -/
def originalSourceLocalizedBoundaryMap :
    let _ := normalizedOriginalChartAlgebra f hL d V c k n o W U hU hUW
    let _ := normalizedOriginalBoundaryAlgebra f hL d V c k n o W U hU hUW
    LocalizedModule M Sinv →ₗ[Localization M] LocalizedModule M Bsource := by
  let _ := normalizedOriginalChartAlgebra f hL d V c k n o W U hU hUW
  let _ := normalizedOriginalBoundaryAlgebra f hL d V c k n o W U hU hUW
  exact LocalizedModule.map M (α).toLinearMap

/-- The original denominator cancels against the exact scaled boundary. -/
theorem originalSourceLocalizedBoundaryMap_fraction (x : M) (w : Sinv) (t : Bsource)
    (hw : normalizedBoundaryChartMap f hL d V c k n o U hU w =
      normalizedBoundaryChartMap f hL d V c k n o U hU (σ x.val) * t) :
    let _ := normalizedOriginalChartAlgebra f hL d V c k n o W U hU hUW
    let _ := normalizedOriginalBoundaryAlgebra f hL d V c k n o W U hU hUW
    originalSourceLocalizedBoundaryMap f hL d V c k n o W U hU hUW P
      (LocalizedModule.mk w x) = LocalizedModule.mk t 1 := by
  let _ := normalizedOriginalChartAlgebra f hL d V c k n o W U hU hUW
  let _ := normalizedOriginalBoundaryAlgebra f hL d V c k n o W U hU hUW
  change LocalizedModule.map M (α).toLinearMap (LocalizedModule.mk w x) = _
  rw [LocalizedModule.map_mk]
  have hw' : α w = x • t := hw
  change LocalizedModule.mk (α w) x = LocalizedModule.mk t 1
  rw [hw']
  exact LocalizedModule.mk_cancel x t

attribute [local irreducible] originalSourceLocalizedBoundaryMap

include ha in
/-- Preserve the invariant boundary value when constructing the full source numerator. -/
theorem originalSource_pairOpen_boundary_numerator
    (hP : PrimeSpectrum.comap κ ⟨P, inferInstance⟩ ∈
      SchemeScalarPrincipalNeighborhood.scalarNeighborhoodLocus σ₀ O)
    (v : invariantCoordinates (restrictedAction τU O hO)) (t : Bsource)
    (hb : ((jU) ∣_ O).appTop v.val = ((jU) ⁻¹ᵁ O).ι.appTop t.val)
    (he : (pairOpenFirst O F H).appTop v.val = (pairOpenSecond O F H).appTop v.val) :
    ∃ x₀ : Ω, κ x₀ ∉ P ∧ ∃ w : Sinv,
      normalizedBoundaryChartMap f hL d V c k n o U hU w =
        normalizedBoundaryChartMap f hL d V c k n o U hU (σ x₀) * t ∧
      w.val ∈ SchemeEffectiveEpiSections.compatibleFunctions F H := by
  obtain ⟨x₀, hx, w, hw, hrel⟩ := originalSource_pairOpen_lift
    f hL d V c k n o W U hU hUW ha O hO P hP v t.val hb he
  exact ⟨x₀, hx, w, Subtype.ext hw, hrel⟩

include ha in
/-- Invert the original scalar to lift the unscaled boundary coefficient exactly. -/
theorem originalSource_pairOpen_localized_lift
    (hP : PrimeSpectrum.comap κ ⟨P, inferInstance⟩ ∈
      SchemeScalarPrincipalNeighborhood.scalarNeighborhoodLocus σ₀ O)
    (v : invariantCoordinates (restrictedAction τU O hO)) (t : Bsource)
    (hb : ((jU) ∣_ O).appTop v.val = ((jU) ⁻¹ᵁ O).ι.appTop t.val)
    (he : (pairOpenFirst O F H).appTop v.val = (pairOpenSecond O F H).appTop v.val) :
    let _ := normalizedOriginalChartAlgebra f hL d V c k n o W U hU hUW
    let _ := normalizedOriginalBoundaryAlgebra f hL d V c k n o W U hU hUW
    ∃ (x₀ : M) (w : Sinv),
      w.val ∈ SchemeEffectiveEpiSections.compatibleFunctions F H ∧
      originalSourceLocalizedBoundaryMap f hL d V c k n o W U hU hUW P
        (LocalizedModule.mk w x₀) =
        LocalizedModule.mk t 1 := by
  obtain ⟨x₀, hx, w, hw, hrel⟩ := originalSource_pairOpen_boundary_numerator
    f hL d V c k n o W U hU hUW ha O hO P hP v t hb he
  let _ := normalizedOriginalChartAlgebra f hL d V c k n o W U hU hUW
  let _ := normalizedOriginalBoundaryAlgebra f hL d V c k n o W U hU hUW
  exact ⟨⟨x₀, hx⟩, w, hrel, originalSourceLocalizedBoundaryMap_fraction
    f hL d V c k n o W U hU hUW P ⟨x₀, hx⟩ w t hw⟩

end FLT.Mazur.HilbertChart.AffineRestriction
