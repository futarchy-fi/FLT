/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationSubframeTransferBoundary
public import FLT.Mazur.HilbertSubframeBoundaryLifts
public import FLT.Mazur.HilbertNormalizedOrbitBoundaryCoefficients

/-!
# Invariant subframe transfer of original Hilbert boundary lifts

Transfer independent smaller-chart lifts by summing over unordered selections.
This produces an invariant lift of the binomial multiple and an invariant
boundary-zero correction from any independent larger-chart lift. The construction
uses the original boundary and needs no invertibility of the binomial coefficient.
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

variable (m' : ℕ) (a : Fin m')
  (U' : (normalizedFullRelationFrames f hL d V c k m' a).Opens)
  (hU' : ∀ σ : Equiv.Perm (Fin m'),
    (normalizedFullRelationAction f hL d V c k m' a σ).hom ⁻¹ᵁ U' = U')
  (h : ∀ ι : Fin m' ↪ Fin n,
    U ≤ subframeMap (fullRelationSchemeEquivalence f hL d V c k) o a ι ⁻¹ᵁ U')
  (hU'W : U' ≤ normalizedFullRelationFirst f hL d V c k m' a ⁻¹ᵁ
    (pullOpen (equivalence f hL d V c k) W).val)
  (t : (invariantSheaf (originalClosedEquivalence f hL d V c k)).obj.obj
    (op ((TopologicalSpace.Opens.map (originalClosedInvariantMap f hL d V c k).base).obj W)))

/-- Unordered transfer gives the exact binomial multiple of the original Hilbert coefficient. -/
theorem normalizedOrbitBoundary_subframeTransfer
    (v : invariantCoordinates (restrictedAction
      (normalizedFullRelationAction f hL d V c k m' a) U' hU'))
    (hv : normalizedBoundaryChartMap f hL d V c k m' a U' hU' v =
      normalizedOrbitBoundaryCoefficient f hL d V c k m' a W U' hU' hU'W t) :
    normalizedBoundaryChartMap f hL d V c k n o U hU
      (subframeTransfer e o a U hU U' hU' h v) =
        n.choose m' • normalizedOrbitBoundaryCoefficient f hL d V c k n o W U hU hUW t := by
  apply Subtype.ext
  change ((j) ∣_ U).appTop (subframeTransferSection e o a U U' hU' h v) = _
  unfold subframeTransferSection
  rw [map_sum]
  simp only [normalizedOrbitBoundaryLift_subframeRefinement f hL d V c k n o W
    U hU hUW m' a _ U' hU' _ hU'W t v hv, Finset.sum_const, Finset.card_univ,
    SubframeSelections.card, Fintype.card_fin]
  rfl

/-- The independent Hilbert source lift differs from transfer by an invariant kernel element. -/
theorem normalizedOrbitBoundary_subframeTransferCorrection_zero
    (u : invariantCoordinates (restrictedAction τ U hU))
    (v : invariantCoordinates (restrictedAction
      (normalizedFullRelationAction f hL d V c k m' a) U' hU'))
    (hu : normalizedBoundaryChartMap f hL d V c k n o U hU u =
      normalizedOrbitBoundaryCoefficient f hL d V c k n o W U hU hUW t)
    (hv : normalizedBoundaryChartMap f hL d V c k m' a U' hU' v =
      normalizedOrbitBoundaryCoefficient f hL d V c k m' a W U' hU' hU'W t) :
    normalizedBoundaryChartMap f hL d V c k n o U hU
      (subframeTransferCorrection e o a U hU U' hU' h u v) = 0 := by
  rw [subframeTransferCorrection, map_sub, map_nsmul, hu,
    normalizedOrbitBoundary_subframeTransfer f hL d V c k n o W U hU hUW
      m' a U' hU' h hU'W t v hv]
  simp only [Fintype.card_fin, sub_self]

/-- Affine independent charts construct both exact lifts and the invariant transfer correction. -/
theorem exists_originalSubframe_transfer_correction (ha : IsAffineOpen U)
    (ha' : IsAffineOpen U') :
    ∃ (u : invariantCoordinates (restrictedAction τ U hU))
      (v : invariantCoordinates (restrictedAction
        (normalizedFullRelationAction f hL d V c k m' a) U' hU')),
      normalizedBoundaryChartMap f hL d V c k n o U hU u =
        normalizedOrbitBoundaryCoefficient f hL d V c k n o W U hU hUW t ∧
      normalizedBoundaryChartMap f hL d V c k m' a U' hU' v =
        normalizedOrbitBoundaryCoefficient f hL d V c k m' a W U' hU' hU'W t ∧
      normalizedBoundaryChartMap f hL d V c k n o U hU
        (subframeTransferCorrection e o a U hU U' hU' h u v) = 0 := by
  obtain ⟨u, hu⟩ := normalizedOrbitBoundaryCoefficient_lift f hL d V c k n o W U hU hUW t ha
  obtain ⟨v, hv⟩ := normalizedOrbitBoundaryCoefficient_lift f hL d V c k m' a W
    U' hU' hU'W t ha'
  exact ⟨u, v, hu, hv, normalizedOrbitBoundary_subframeTransferCorrection_zero
    f hL d V c k n o W U hU hUW m' a U' hU' h hU'W t u v hu hv⟩

end FLT.Mazur.HilbertChart.AffineRestriction
