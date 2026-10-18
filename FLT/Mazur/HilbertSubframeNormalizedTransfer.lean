/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationSubframeNormalizedCorrection
public import FLT.Mazur.HilbertSubframeTransferCorrections
public import FLT.Mazur.HilbertSubframeBoundaryLifts
public import FLT.Mazur.HilbertNormalizedOrbitBoundaryCoefficients

/-!
# Exact unscaled transfer of original Hilbert boundary coefficients

On a chart where the binomial degree is a unit, normalized transfer gives an
invariant lift of the original coefficient. This uses the unreduced boundary.
It does not assert the remaining selection errors or original graph equations.
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

variable (hN : IsUnit (n.choose m' : Γ(U.toScheme, ⊤)))
local notation "hdeg" => (show IsUnit
  ((Fintype.card (Fin n)).choose (Fintype.card (Fin m')) : Γ(U.toScheme, ⊤)) from
    by simpa only [Fintype.card_fin] using hN)

/-- Normalization lifts the original Hilbert coefficient without a binomial multiple. -/
theorem normalizedOrbitBoundary_subframeNormalizedTransfer
    (v : invariantCoordinates (restrictedAction
      (normalizedFullRelationAction f hL d V c k m' a) U' hU'))
    (hv : normalizedBoundaryChartMap f hL d V c k m' a U' hU' v =
      normalizedOrbitBoundaryCoefficient f hL d V c k m' a W U' hU' hU'W t) :
    normalizedBoundaryChartMap f hL d V c k n o U hU
      (subframeNormalizedTransfer e o a U hU U' hU' h hdeg v) =
        normalizedOrbitBoundaryCoefficient f hL d V c k n o W U hU hUW t := by
  apply Subtype.ext
  apply subframeNormalizedTransfer_map e o a U hU U' hU' h hdeg ((j) ∣_ U).appTop.hom
  have hh := congrArg Subtype.val (normalizedOrbitBoundary_subframeTransfer
    f hL d V c k n o W U hU hUW m' a U' hU' h hU'W t v hv)
  change ((j) ∣_ U).appTop (subframeTransferSection e o a U U' hU' h v) =
    n.choose m' • (normalizedOrbitBoundaryCoefficient f hL d V c k n o W U hU hUW t).val
      at hh
  simpa only [Fintype.card_fin] using hh

/-- Independent original source lifts have an actual unscaled invariant kernel correction. -/
theorem normalizedOrbitBoundary_subframeNormalizedCorrection_zero
    (u : invariantCoordinates (restrictedAction τ U hU))
    (v : invariantCoordinates (restrictedAction
      (normalizedFullRelationAction f hL d V c k m' a) U' hU'))
    (hu : normalizedBoundaryChartMap f hL d V c k n o U hU u =
      normalizedOrbitBoundaryCoefficient f hL d V c k n o W U hU hUW t)
    (hv : normalizedBoundaryChartMap f hL d V c k m' a U' hU' v =
      normalizedOrbitBoundaryCoefficient f hL d V c k m' a W U' hU' hU'W t) :
    normalizedBoundaryChartMap f hL d V c k n o U hU
      (subframeNormalizedCorrection e o a U hU U' hU' h hdeg u v) = 0 := by
  rw [subframeNormalizedCorrection, map_sub, hu,
    normalizedOrbitBoundary_subframeNormalizedTransfer f hL d V c k n o W U hU hUW
      m' a U' hU' h hU'W t hN v hv, sub_self]

/-- An affine target gives an unscaled lift on the source without assuming source affineness. -/
theorem exists_originalSubframe_normalized_lift (ha' : IsAffineOpen U') :
    ∃ (v : invariantCoordinates (restrictedAction
        (normalizedFullRelationAction f hL d V c k m' a) U' hU')),
      normalizedBoundaryChartMap f hL d V c k m' a U' hU' v =
        normalizedOrbitBoundaryCoefficient f hL d V c k m' a W U' hU' hU'W t ∧
      normalizedBoundaryChartMap f hL d V c k n o U hU
        (subframeNormalizedTransfer e o a U hU U' hU' h hdeg v) =
          normalizedOrbitBoundaryCoefficient f hL d V c k n o W U hU hUW t := by
  obtain ⟨v, hv⟩ := normalizedOrbitBoundaryCoefficient_lift f hL d V c k m' a W
    U' hU' hU'W t ha'
  exact ⟨v, hv, normalizedOrbitBoundary_subframeNormalizedTransfer
    f hL d V c k n o W U hU hUW m' a U' hU' h hU'W t hN v hv⟩

end FLT.Mazur.HilbertChart.AffineRestriction
