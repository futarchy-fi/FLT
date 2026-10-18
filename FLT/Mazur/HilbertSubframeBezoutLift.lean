/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertSubframeTransferCorrections
public import FLT.Mazur.BinomialBezoutCombination

/-!
# Integral Hilbert boundary lifts from independent strict subframes

For a non-prime-power source size, combine transfers from all positive strict
sizes with constructed integral Bezout coefficients. This lifts the original
boundary coefficient globally on the supplied common selection domain, without
any unit-degree or source-affineness assumption. It does not solve graph errors.
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

variable (hn : 1 < n) (hp : ¬ IsPrimePow n)
  (a : ∀ idx : BinomialBezoutCombination.Sizes n, Fin idx.val)
  (Us : (idx : BinomialBezoutCombination.Sizes n) →
    (normalizedFullRelationFrames f hL d V c k idx.val (a idx)).Opens)
  (hUs : ∀ (idx : BinomialBezoutCombination.Sizes n) σ,
    (normalizedFullRelationAction f hL d V c k idx.val (a idx) σ).hom ⁻¹ᵁ Us idx = Us idx)
  (hUsW : ∀ idx : BinomialBezoutCombination.Sizes n,
    Us idx ≤ normalizedFullRelationFirst f hL d V c k idx.val (a idx) ⁻¹ᵁ
    (pullOpen (equivalence f hL d V c k) W).val)
  (hSel : ∀ (idx : BinomialBezoutCombination.Sizes n) (ι : Fin idx.val ↪ Fin n), U ≤
    subframeMap (fullRelationSchemeEquivalence f hL d V c k) o (a idx) ι ⁻¹ᵁ Us idx)
  (t : (invariantSheaf (originalClosedEquivalence f hL d V c k)).obj.obj
    (op ((TopologicalSpace.Opens.map (originalClosedInvariantMap f hL d V c k).base).obj W)))

/-- Combine actual transfers with the constructed integral degree-one coefficients. -/
@[irreducible] def originalSubframeBezoutLift
    (v : ∀ idx : BinomialBezoutCombination.Sizes n,
      invariantCoordinates (restrictedAction
      (normalizedFullRelationAction f hL d V c k idx.val (a idx)) (Us idx) (hUs idx))) :
    invariantCoordinates (restrictedAction τ U hU) :=
  BinomialBezoutCombination.combine n hn hp fun idx ↦
    subframeTransfer e o (a idx) U hU (Us idx) (hUs idx) (hSel idx) (v idx)

/-- All strict-size transfers combine to the exact original coefficient with no inversion. -/
theorem normalizedOrbitBoundary_subframeBezoutLift
    (v : ∀ idx : BinomialBezoutCombination.Sizes n,
      invariantCoordinates (restrictedAction
      (normalizedFullRelationAction f hL d V c k idx.val (a idx)) (Us idx) (hUs idx)))
    (hv : ∀ idx : BinomialBezoutCombination.Sizes n,
      normalizedBoundaryChartMap f hL d V c k idx.val (a idx) (Us idx) (hUs idx) (v idx) =
      normalizedOrbitBoundaryCoefficient f hL d V c k idx.val (a idx) W
        (Us idx) (hUs idx) (hUsW idx) t) :
    normalizedBoundaryChartMap f hL d V c k n o U hU
      (originalSubframeBezoutLift f hL d V c k n o U hU hn hp a Us hUs hSel v) =
        normalizedOrbitBoundaryCoefficient f hL d V c k n o W U hU hUW t := by
  rw [originalSubframeBezoutLift]
  apply BinomialBezoutCombination.map_combine_scaled n hn hp
    (normalizedBoundaryChartMap f hL d V c k n o U hU).toAddMonoidHom
  intro idx
  exact normalizedOrbitBoundary_subframeTransfer f hL d V c k n o W U hU hUW
    idx.val (a idx) (Us idx) (hUs idx) (hSel idx) (hUsW idx) t (v idx) (hv idx)

/-- The integral construction corrects any independent invariant source lift in the kernel. -/
theorem normalizedOrbitBoundary_subframeBezoutCorrection_zero
    (u : invariantCoordinates (restrictedAction τ U hU))
    (hu : normalizedBoundaryChartMap f hL d V c k n o U hU u =
      normalizedOrbitBoundaryCoefficient f hL d V c k n o W U hU hUW t)
    (v : ∀ idx : BinomialBezoutCombination.Sizes n,
      invariantCoordinates (restrictedAction
      (normalizedFullRelationAction f hL d V c k idx.val (a idx)) (Us idx) (hUs idx)))
    (hv : ∀ idx : BinomialBezoutCombination.Sizes n,
      normalizedBoundaryChartMap f hL d V c k idx.val (a idx) (Us idx) (hUs idx) (v idx) =
      normalizedOrbitBoundaryCoefficient f hL d V c k idx.val (a idx) W
        (Us idx) (hUs idx) (hUsW idx) t) :
    normalizedBoundaryChartMap f hL d V c k n o U hU
      (u - originalSubframeBezoutLift f hL d V c k n o U hU hn hp a Us hUs hSel v) = 0 := by
  rw [map_sub, hu, normalizedOrbitBoundary_subframeBezoutLift
    f hL d V c k n o W U hU hUW hn hp a Us hUs hUsW hSel t v hv, sub_self]

/-- Independent affine targets construct an integral unscaled lift on the common source. -/
theorem exists_originalSubframe_bezout_lift (ha : ∀ idx, IsAffineOpen (Us idx)) :
    ∃ v : ∀ idx : BinomialBezoutCombination.Sizes n,
      invariantCoordinates (restrictedAction
        (normalizedFullRelationAction f hL d V c k idx.val (a idx)) (Us idx) (hUs idx)),
      (∀ idx : BinomialBezoutCombination.Sizes n,
        normalizedBoundaryChartMap f hL d V c k idx.val (a idx) (Us idx) (hUs idx) (v idx) =
        normalizedOrbitBoundaryCoefficient f hL d V c k idx.val (a idx) W
          (Us idx) (hUs idx) (hUsW idx) t) ∧
      normalizedBoundaryChartMap f hL d V c k n o U hU
        (originalSubframeBezoutLift f hL d V c k n o U hU hn hp a Us hUs hSel v) =
          normalizedOrbitBoundaryCoefficient f hL d V c k n o W U hU hUW t := by
  have hex : ∀ idx : BinomialBezoutCombination.Sizes n, ∃ v,
      normalizedBoundaryChartMap f hL d V c k idx.val (a idx) (Us idx) (hUs idx) v =
        normalizedOrbitBoundaryCoefficient f hL d V c k idx.val (a idx) W
          (Us idx) (hUs idx) (hUsW idx) t := fun idx ↦
    normalizedOrbitBoundaryCoefficient_lift f hL d V c k idx.val (a idx) W
      (Us idx) (hUs idx) (hUsW idx) t (ha idx)
  choose v hv using hex
  exact ⟨v, hv, normalizedOrbitBoundary_subframeBezoutLift
    f hL d V c k n o W U hU hUW hn hp a Us hUs hUsW hSel t v hv⟩

end FLT.Mazur.HilbertChart.AffineRestriction
