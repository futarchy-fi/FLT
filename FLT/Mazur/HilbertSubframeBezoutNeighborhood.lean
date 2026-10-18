/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertSubframeBezoutLift
public import FLT.Mazur.HilbertSubframeAffineTargets

/-!
# Constructed neighborhoods for integral unscaled Hilbert lifts

At every original frame point of non-prime-power size, independently construct
stable affine targets for all positive strict sizes and a common stable affine
source. Their integral transfers lift the original boundary coefficient. No
target charts, all-selection inclusions, or binomial units are assumed.
The remaining embedding errors are not asserted to vanish.
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

attribute [local irreducible] normalizedBoundaryChartMap normalizedOrbitBoundaryCoefficient

variable (hn : 1 < n) (hp : ¬ IsPrimePow n)
  (a : ∀ idx : BinomialBezoutCombination.Sizes n, Fin idx.val)
  (t : (invariantSheaf (originalClosedEquivalence f hL d V c k)).obj.obj
    (op ((TopologicalSpace.Opens.map (originalClosedInvariantMap f hL d V c k).base).obj W)))

include hU in
/-- Actual source points have unscaled integral lifts on constructed simultaneous targets. -/
theorem exists_originalSubframe_bezout_neighborhood
    (x : normalizedFullRelationFrames f hL d V c k n o) (hxU : x ∈ U)
    (hxW : normalizedFullRelationFirst f hL d V c k n o x ∈ (pullOpen eo W).val) :
    ∃ (Us : (idx : BinomialBezoutCombination.Sizes n) →
        (normalizedFullRelationFrames f hL d V c k idx.val (a idx)).Opens)
      (hUs : ∀ (idx : BinomialBezoutCombination.Sizes n) σ,
        (normalizedFullRelationAction f hL d V c k idx.val (a idx) σ).hom
        ⁻¹ᵁ Us idx = Us idx)
      (hUsW : ∀ idx : BinomialBezoutCombination.Sizes n,
        Us idx ≤ normalizedFullRelationFirst f hL d V c k idx.val (a idx)
        ⁻¹ᵁ (pullOpen eo W).val)
      (Z : (normalizedFullRelationFrames f hL d V c k n o).Opens)
      (hZ : ∀ σ, (τ σ).hom ⁻¹ᵁ Z = Z)
      (hZW : Z ≤ normalizedFullRelationFirst f hL d V c k n o ⁻¹ᵁ (pullOpen eo W).val),
      (∀ idx, IsAffineOpen (Us idx)) ∧ IsAffineOpen Z ∧ x ∈ Z ∧ Z ≤ U ∧
      ∃ hSel : ∀ (idx : BinomialBezoutCombination.Sizes n) (ι : Fin idx.val ↪ Fin n),
          Z ≤ subframeMap e o (a idx) ι ⁻¹ᵁ Us idx,
      ∃ v : ∀ idx : BinomialBezoutCombination.Sizes n,
          invariantCoordinates (restrictedAction
            (normalizedFullRelationAction f hL d V c k idx.val (a idx)) (Us idx) (hUs idx)),
        (∀ idx : BinomialBezoutCombination.Sizes n,
          normalizedBoundaryChartMap f hL d V c k idx.val (a idx)
          (Us idx) (hUs idx) (v idx) =
          normalizedOrbitBoundaryCoefficient f hL d V c k idx.val (a idx) W
            (Us idx) (hUs idx) (hUsW idx) t) ∧
        normalizedBoundaryChartMap f hL d V c k n o Z hZ
          (originalSubframeBezoutLift f hL d V c k n o Z hZ hn hp a Us hUs hSel v) =
          normalizedOrbitBoundaryCoefficient f hL d V c k n o W Z hZ hZW t := by
  obtain ⟨Us, ha, hUsW, hUs, Z, hZaff, hxZ, hZU, hZW, hZ, hSel⟩ :=
    exists_normalized_subframe_affine_family f hL d V c k n o
      (pullOpen eo W).val (pullOpen_preimage_eq eo W) U hU
      (fun idx : BinomialBezoutCombination.Sizes n ↦ idx.val) a x hxU hxW
  refine ⟨Us, hUs, hUsW, Z, hZ, hZW, ha, hZaff, hxZ, hZU, hSel, ?_⟩
  exact exists_originalSubframe_bezout_lift f hL d V c k n o W Z hZ hZW
    hn hp a Us hUs hUsW hSel t ha

end FLT.Mazur.HilbertChart.AffineRestriction
