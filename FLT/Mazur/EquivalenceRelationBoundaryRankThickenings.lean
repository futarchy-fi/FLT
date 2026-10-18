/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationBoundaryComponentRank
public import FLT.Mazur.RelativeRankPullbackThickenings

/-!
# Actual rank thickenings above the full scalar boundary product

First lift the full product to the original normalized chart, then pull back
its ideal-power rank stages. These stages cover the full product at every order,
including residual points. Their coefficients and original boundary primes are
retained; their pointwise cover is not asserted to be a descent cover.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open RelativeOrderedTuples AffineScalarBoundaryNilpotence
open FiniteGroupRestriction SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] source action restrictedAction boundaryProduct boundaryProjection
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] (n : ℕ) (o : Fin n) (U : (source p q (Fin n) o).Opens)
  (e : CategoryTheory.EquivalenceRelation p q)
  (hU : ∀ g : Equiv.Perm (Fin n), (action e (Fin n) o g).hom ⁻¹ᵁ U = U)
  [IsAffine U.toScheme]
  {R T : Type} [CommRing R] [CommRing T]
  (s : R →+* invariantCoordinates (restrictedAction (action e (Fin n) o) U hU))
  (κ : R →+* T)
local instance rankBoundaryOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance rankBoundaryOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance rankBoundaryOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
local notation "ρ" => restrictedAction (action e (Fin n) o) U hU

/-- The original chart over the full unchanged invariant scalar boundary product. -/
def chartBoundary : Scheme := pullback (quotientMap ρ) (boundaryProjection s κ)

/-- Retain the actual normalized chart point. -/
def chartBoundaryChart : chartBoundary n o U e hU s κ ⟶ U.toScheme := pullback.fst _ _

/-- Retain the actual full scalar product point. -/
def chartBoundaryProduct : chartBoundary n o U e hU s κ ⟶ boundaryProduct s κ :=
  pullback.snd _ _

omit [Etale p] [QuasiCompact p] in
/-- No point of the full scalar product is lost by lifting to the original chart. -/
theorem chartBoundaryProduct_surjective :
    Function.Surjective (chartBoundaryProduct n o U e hU s κ) := by
  intro z
  obtain ⟨x, hx⟩ := (quotientMap ρ).surjective (boundaryProjection s κ z)
  exact (Scheme.Pullback.exists_preimage_pullback x z hx).imp fun _ h ↦ h.2

/-- The unchanged original endpoint on the chart boundary. -/
def chartBoundaryEndpoint : chartBoundary n o U e hU s κ ⟶ A :=
  chartBoundaryChart n o U e hU s κ ≫ U.ι ≫ first p q (Fin n) o

/-- Every point of the full product lifts to an actual thickened original rank piece. -/
theorem exists_boundary_rankThickening_lift (k : ℕ) (z : boundaryProduct s κ) :
    ∃ (m : ℕ) (y : rankPullbackThickening (Over.mk p)
      (chartBoundaryEndpoint n o U e hU s κ) m k),
      chartBoundaryProduct n o U e hU s κ
        (rankPullbackMap (Over.mk p) (chartBoundaryEndpoint n o U e hU s κ) m k y) = z := by
  obtain ⟨x, hx⟩ := chartBoundaryProduct_surjective n o U e hU s κ z
  obtain ⟨m, y, hy⟩ := exists_rankPullback_lift (Over.mk p)
    (chartBoundaryEndpoint n o U e hU s κ) k x
  exact ⟨m, y, by rw [hy, hx]⟩

omit [QuasiCompact p] [IsAffine U.toScheme] in
/-- Exact-rank stages below the size of the retained original frame are empty. -/
theorem boundary_rankThickening_empty_below (m k : ℕ) (hm : m < n) :
    IsEmpty (rankPullbackThickening (Over.mk p)
      (chartBoundaryEndpoint n o U e hU s κ) m k) := by
  refine ⟨fun y ↦ ?_⟩
  have hr := rankPullback_endpoint (Over.mk p)
    (chartBoundaryEndpoint n o U e hU s κ) m k y
  let x := chartBoundaryChart n o U e hU s κ
    (rankPullbackMap (Over.mk p) (chartBoundaryEndpoint n o U e hU s κ) m k y)
  have hn : first p q (Fin n) o (U.ι x) ∈ rankImageOpen (Over.mk p) n :=
    ⟨inclusion p q (Fin n) o (U.ι x), rfl⟩
  exact hr.2 (rankImageOpen_antitone (Over.mk p) hm hn)

end FLT.Mazur.EquivalenceRelationNormalizedFrames
