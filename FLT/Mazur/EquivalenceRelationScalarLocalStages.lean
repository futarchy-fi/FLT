/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationScalarLocalRanks
public import FLT.Mazur.RelativeRankThickeningFinite

/-!
# Bounded rank stages on the entire original scalar local scheme

The original finite flat chart remains faithful over the full scalar local
product. Every point lifts to a stage between the retained frame size and
the computed scalar ceiling. Stage maps cover points; they are not asserted
to be flat or to recover all coefficients simultaneously.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open RelativeOrderedTuples AffineScalarBoundaryNilpotence
open FiniteGroupRestriction SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] source action restrictedAction boundaryProduct
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p] [QuasiCompact p]
  (n : ℕ) (o : Fin n) (U : (source p q (Fin n) o).Opens)
  (e : CategoryTheory.EquivalenceRelation p q)
  (hU : ∀ g : Equiv.Perm (Fin n), (action e (Fin n) o g).hom ⁻¹ᵁ U = U)
  [IsAffine U.toScheme]
  {R T : Type} [CommRing R] [CommRing T]
  (s : R →+* invariantCoordinates (restrictedAction (action e (Fin n) o) U hU))
  (κ : R →+* T)
local notation "π" => chartBoundaryProduct n o U e hU s κ
local notation "b" => chartBoundaryEndpoint n o U e hU s κ
local notation "ρ" => restrictedAction (action e (Fin n) o) U hU
local instance scalarLocalStageOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance scalarLocalStageOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance scalarLocalStageOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›

variable (P : PrimeSpectrum T)
local notation "l" => boundaryScalarLocalMap s κ P
local notation "localProduct" => boundaryScalarLocalProduct s κ P

/-- The full faithful chart after localization at the original scalar prime. -/
def boundaryScalarLocalChart : Scheme := pullback π l

/-- The coefficient projection onto the entire original scalar-localized product. -/
def boundaryScalarLocalProjection : boundaryScalarLocalChart n o U e hU s κ P ⟶ localProduct :=
  pullback.snd _ _

/-- The unchanged original relation endpoint on this full scalar local chart. -/
def boundaryScalarLocalEndpoint : boundaryScalarLocalChart n o U e hU s κ P ⟶ A :=
  pullback.fst π l ≫ b

instance boundaryScalarLocalProjection_finite :
    IsFinite (boundaryScalarLocalProjection n o U e hU s κ P) := by
  unfold boundaryScalarLocalProjection
  infer_instance

instance boundaryScalarLocalProjection_flat :
    Flat (boundaryScalarLocalProjection n o U e hU s κ P) := by
  unfold boundaryScalarLocalProjection
  infer_instance

instance boundaryScalarLocalProjection_surjective :
    Surjective (boundaryScalarLocalProjection n o U e hU s κ P) := by
  unfold boundaryScalarLocalProjection
  infer_instance

instance boundaryScalarLocalChart_affine :
    IsAffine (boundaryScalarLocalChart n o U e hU s κ P) :=
  isAffine_of_isAffineHom (boundaryScalarLocalProjection n o U e hU s κ P)

instance boundaryScalarLocalProjection_effectiveEpi :
    EffectiveEpi (boundaryScalarLocalProjection n o U e hU s κ P) := by infer_instance

local notation "δ" => boundaryScalarLocalProjection n o U e hU s κ P
local notation "endpoint" => boundaryScalarLocalEndpoint n o U e hU s κ P
local notation "rankOf" => boundaryPointRank n o U e hU s κ

/-- Every chart lift has precisely the computed rank of its full local coefficient point. -/
theorem boundaryScalarLocalEndpoint_rank_iff
    (x : boundaryScalarLocalChart n o U e hU s κ P) (m : ℕ) :
    endpoint x ∈ exactRank (Over.mk p) m ↔ rankOf (l (δ x)) = m := by
  have hc : π (pullback.fst π l x) = l (δ x) :=
    congrArg (fun f ↦ f x) (pullback.condition (f := π) (g := l))
  rw [boundaryPointRank_eq_iff, ← hc]
  have he := Set.ext_iff.mp (boundaryExactRank_preimage n o U e hU s κ m)
    (pullback.fst π l x)
  exact he.symm

/-- The actual map from a finite rank order into the whole scalar-localized product. -/
def boundaryScalarLocalRankMap (m k : ℕ) :
    rankPullbackThickening (Over.mk p) endpoint m k ⟶ localProduct :=
  rankPullbackMap (Over.mk p) endpoint m k ≫ δ

/-- Every point of every rank order has exactly that rank in the original product. -/
theorem boundaryScalarLocalRankMap_rank (m k : ℕ)
    (x : rankPullbackThickening (Over.mk p) endpoint m k) :
    rankOf (l (boundaryScalarLocalRankMap n o U e hU s κ P m k x)) = m :=
  (boundaryScalarLocalEndpoint_rank_iff n o U e hU s κ P _ m).mp
    (rankPullback_endpoint (Over.mk p) endpoint m k x)

variable [TopologicalSpace.NoetherianSpace A]
local notation "ceiling" => boundaryScalarRankCeiling n o U e hU s κ P

/-- Every original local point lifts to a rank stage in the finite, computed scalar interval. -/
theorem exists_boundaryScalarLocal_rank_stage (k : ℕ) (z : localProduct) :
    ∃ (m : ℕ) (x : rankPullbackThickening (Over.mk p) endpoint m k),
      n ≤ m ∧ m ≤ ceiling ∧ boundaryScalarLocalRankMap n o U e hU s κ P m k x = z := by
  obtain ⟨y, hy⟩ := (boundaryScalarLocalProjection_surjective n o U e hU s κ P).surj z
  let m := rankOf (l z)
  have hr : endpoint y ∈ exactRank (Over.mk p) m := by
    apply (boundaryScalarLocalEndpoint_rank_iff n o U e hU s κ P y m).mpr
    simp only [hy, m]
  have hm : y ∈ Set.range (rankPullbackMap (Over.mk p) endpoint m k) := by
    rw [rankPullbackMap_range]
    exact hr
  obtain ⟨x, hx⟩ := hm
  have hb := boundaryScalarLocal_point_rank_bounds n o U e hU s κ P z
  refine ⟨m, x, hb.1, hb.2, ?_⟩
  change δ (rankPullbackMap (Over.mk p) endpoint m k x) = z
  rwa [hx]

/-- Stages above the computed scalar ceiling are empty on the entire local chart. -/
theorem boundaryScalarLocal_rank_stage_empty_above (m k : ℕ) (hm : ceiling < m) :
    IsEmpty (rankPullbackThickening (Over.mk p) endpoint m k) := by
  refine ⟨fun x ↦ ?_⟩
  have hb := (boundaryScalarLocal_point_rank_bounds n o U e hU s κ P
    (boundaryScalarLocalRankMap n o U e hU s κ P m k x)).2
  rw [boundaryScalarLocalRankMap_rank] at hb
  exact (Nat.not_le_of_lt hm) hb

/-- Stages below the retained frame size are also empty on the entire local chart. -/
theorem boundaryScalarLocal_rank_stage_empty_below (m k : ℕ) (hm : m < n) :
    IsEmpty (rankPullbackThickening (Over.mk p) endpoint m k) := by
  refine ⟨fun x ↦ ?_⟩
  have hb := (boundaryScalarLocal_point_rank_bounds n o U e hU s κ P
    (boundaryScalarLocalRankMap n o U e hU s κ P m k x)).1
  rw [boundaryScalarLocalRankMap_rank] at hb
  exact (Nat.not_le_of_lt hm) hb

variable [LocallyQuasiFinite p]
local instance scalarLocalStageOver_quasiFinite : LocallyQuasiFinite (Over.mk p).hom :=
  ‹LocallyQuasiFinite p›

omit [IsAffine U.toScheme] [TopologicalSpace.NoetherianSpace A] in
/-- The whole original relation becomes finite on each unsplit local rank stage. -/
theorem boundaryScalarLocal_rank_stage_finite (m k : ℕ) :
    IsFinite (pullback.snd p (rankPullbackMap (Over.mk p) endpoint m k ≫ endpoint)) :=
  finite_pullback_rankPullback (Over.mk p) endpoint m k

end FLT.Mazur.EquivalenceRelationNormalizedFrames
