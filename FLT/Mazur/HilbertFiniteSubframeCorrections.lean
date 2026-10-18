/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertSubframeBoundaryLifts
public import FLT.Mazur.HilbertFiniteSubframeRefinement

/-!
# Local corrections for finite independently sized chart families

Construct the stable affine source chart and an invariant lift of the original
boundary section. Every independent smaller-chart lift then has an explicit
boundary-zero error on this one source chart, for each embedding separately.
These are raw section corrections; their invariant descent remains a separate problem.
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
variable (t : (invariantSheaf (originalClosedEquivalence f hL d V c k)).obj.obj
  (op ((TopologicalSpace.Opens.map (originalClosedInvariantMap f hL d V c k).base).obj W)))

/-- Construct all strict-subframe boundary-zero errors on an actual stable affine neighborhood. -/
theorem exists_originalFiniteSubframe_corrections
    (U : (normalizedFullRelationFrames f hL d V c k n o).Opens)
    (hU : ∀ σ, (τ σ).hom ⁻¹ᵁ U = U)
    {T : Type} [Finite T] (sizes : T → ℕ) (a : ∀ idx, Fin (sizes idx))
    (Us : (idx : T) →
      (normalizedFullRelationFrames f hL d V c k (sizes idx) (a idx)).Opens)
    (hUs : ∀ idx σ,
      (normalizedFullRelationAction f hL d V c k (sizes idx) (a idx) σ).hom ⁻¹ᵁ Us idx =
        Us idx)
    (hUsW : ∀ idx, Us idx ≤
      normalizedFullRelationFirst f hL d V c k (sizes idx) (a idx) ⁻¹ᵁ (pullOpen eo W).val)
    (v : ∀ idx, invariantCoordinates
      (restrictedAction (normalizedFullRelationAction f hL d V c k (sizes idx) (a idx))
        (Us idx) (hUs idx)))
    (hv : ∀ idx, normalizedBoundaryChartMap f hL d V c k (sizes idx) (a idx)
      (Us idx) (hUs idx) (v idx) =
      normalizedOrbitBoundaryCoefficient f hL d V c k (sizes idx) (a idx) W
        (Us idx) (hUs idx) (hUsW idx) t)
    (x : normalizedFullRelationFrames f hL d V c k n o) (hxU : x ∈ U)
    (hxW : normalizedFullRelationFirst f hL d V c k n o x ∈ (pullOpen eo W).val)
    (hx : ∀ idx (ι : Fin (sizes idx) ↪ Fin n), subframeMap e o (a idx) ι x ∈ Us idx) :
    ∃ (Z : (normalizedFullRelationFrames f hL d V c k n o).Opens)
      (hZ : ∀ σ, (τ σ).hom ⁻¹ᵁ Z = Z)
      (hZW : Z ≤ normalizedFullRelationFirst f hL d V c k n o ⁻¹ᵁ (pullOpen eo W).val),
      IsAffineOpen Z ∧ x ∈ Z ∧ Z ≤ U ∧
      ∃ hZs : ∀ idx (ι : Fin (sizes idx) ↪ Fin n),
          Z ≤ subframeMap e o (a idx) ι ⁻¹ᵁ Us idx,
        ∃ u : invariantCoordinates (restrictedAction τ Z hZ),
          normalizedBoundaryChartMap f hL d V c k n o Z hZ u =
            normalizedOrbitBoundaryCoefficient f hL d V c k n o W Z hZ hZW t ∧
          ∀ idx (ι : Fin (sizes idx) ↪ Fin n),
            let err := subframeDiscrepancy e o (a idx) ι Z (Us idx) (hZs idx ι)
              u.val (v idx).val
            ((j) ∣_ Z).appTop err = 0 ∧
              u.val - err = (subframeRefinementMap e o (a idx) ι Z (Us idx)
                (hZs idx ι)).appTop (v idx).val := by
  obtain ⟨Z, ha, hxZ, hZU, hZW, hZ, hZs⟩ := exists_normalized_finite_subframe_refinement
    f hL d V c k n o (pullOpen eo W).val (pullOpen_preimage_eq eo W)
    U hU sizes a Us x hxU hxW hx
  obtain ⟨u, hu⟩ := normalizedOrbitBoundaryCoefficient_lift f hL d V c k n o W Z hZ hZW t ha
  refine ⟨Z, hZ, hZW, ha, hxZ, hZU, hZs, u, hu, fun idx ι ↦ ⟨?_, ?_⟩⟩
  · exact normalizedOrbitBoundary_subframeDiscrepancy_zero f hL d V c k n o W Z hZ hZW
      (sizes idx) (a idx) ι (Us idx) (hUs idx) (hZs idx ι) (hUsW idx) t u (v idx) hu (hv idx)
  · exact subframeDiscrepancy_correct e o (a idx) ι Z (Us idx) (hZs idx ι) u.val (v idx).val

/-- Affine target charts supply all independent lifts as well as the local source corrections. -/
theorem exists_originalFiniteSubframe_lifts_and_corrections
    (U : (normalizedFullRelationFrames f hL d V c k n o).Opens)
    (hU : ∀ σ, (τ σ).hom ⁻¹ᵁ U = U)
    {T : Type} [Finite T] (sizes : T → ℕ) (a : ∀ idx, Fin (sizes idx))
    (Us : (idx : T) →
      (normalizedFullRelationFrames f hL d V c k (sizes idx) (a idx)).Opens)
    (hUs : ∀ idx σ,
      (normalizedFullRelationAction f hL d V c k (sizes idx) (a idx) σ).hom ⁻¹ᵁ Us idx =
        Us idx)
    (hUsW : ∀ idx, Us idx ≤
      normalizedFullRelationFirst f hL d V c k (sizes idx) (a idx) ⁻¹ᵁ (pullOpen eo W).val)
    (haUs : ∀ idx, IsAffineOpen (Us idx))
    (x : normalizedFullRelationFrames f hL d V c k n o) (hxU : x ∈ U)
    (hxW : normalizedFullRelationFirst f hL d V c k n o x ∈ (pullOpen eo W).val)
    (hx : ∀ idx (ι : Fin (sizes idx) ↪ Fin n), subframeMap e o (a idx) ι x ∈ Us idx) :
    ∃ v : ∀ idx, invariantCoordinates
      (restrictedAction (normalizedFullRelationAction f hL d V c k (sizes idx) (a idx))
        (Us idx) (hUs idx)),
      (∀ idx, normalizedBoundaryChartMap f hL d V c k (sizes idx) (a idx)
      (Us idx) (hUs idx) (v idx) =
      normalizedOrbitBoundaryCoefficient f hL d V c k (sizes idx) (a idx) W
        (Us idx) (hUs idx) (hUsW idx) t) ∧
    ∃ (Z : (normalizedFullRelationFrames f hL d V c k n o).Opens)
      (hZ : ∀ σ, (τ σ).hom ⁻¹ᵁ Z = Z)
      (hZW : Z ≤ normalizedFullRelationFirst f hL d V c k n o ⁻¹ᵁ (pullOpen eo W).val),
      IsAffineOpen Z ∧ x ∈ Z ∧ Z ≤ U ∧
      ∃ hZs : ∀ idx (ι : Fin (sizes idx) ↪ Fin n),
          Z ≤ subframeMap e o (a idx) ι ⁻¹ᵁ Us idx,
        ∃ u : invariantCoordinates (restrictedAction τ Z hZ),
          normalizedBoundaryChartMap f hL d V c k n o Z hZ u =
            normalizedOrbitBoundaryCoefficient f hL d V c k n o W Z hZ hZW t ∧
          ∀ idx (ι : Fin (sizes idx) ↪ Fin n),
            let err := subframeDiscrepancy e o (a idx) ι Z (Us idx) (hZs idx ι)
              u.val (v idx).val
            ((j) ∣_ Z).appTop err = 0 ∧
              u.val - err = (subframeRefinementMap e o (a idx) ι Z (Us idx)
                (hZs idx ι)).appTop (v idx).val := by
  have hex : ∀ idx, ∃ v,
      normalizedBoundaryChartMap f hL d V c k (sizes idx) (a idx) (Us idx) (hUs idx) v =
        normalizedOrbitBoundaryCoefficient f hL d V c k (sizes idx) (a idx) W
          (Us idx) (hUs idx) (hUsW idx) t := fun idx ↦
    normalizedOrbitBoundaryCoefficient_lift f hL d V c k (sizes idx) (a idx) W
      (Us idx) (hUs idx) (hUsW idx) t (haUs idx)
  choose v hv using hex
  exact ⟨v, hv, exists_originalFiniteSubframe_corrections f hL d V c k n o W t
    U hU sizes a Us hUs hUsW v hv x hxU hxW hx⟩

end FLT.Mazur.HilbertChart.AffineRestriction
