/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationBoundaryComponentBounds
public import FLT.Mazur.RelativeRankStageRecovery

/-!
# Full local coefficient charts at every original minimal component

Localize the actual scalar product at each minimal component, retaining its
entire local ring. The original chart cover remains faithfully flat. Its rank
is constant, and a finite stage of that rank recovers the whole local chart.
The constructed rank need not equal the retained frame size.
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
local instance genericChartOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance genericChartOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance genericChartOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable (Q : minimalPrimes Γ(boundaryProduct s κ, ⊤))
set_option quotPrecheck false
local notation "z" => boundaryComponentPoint s κ Q
local notation "ι" => (boundaryProduct s κ).fromSpecStalk z
local notation "m" => boundaryPointRank n o U e hU s κ z

/-- The chart over the actual local ring of a minimal component of the full scalar product. -/
def boundaryGenericChart : Scheme := pullback π ι

/-- Its coefficient projection retains every nilpotent in that original local ring. -/
def boundaryGenericProjection : boundaryGenericChart n o U e hU s κ Q ⟶
    Spec ((boundaryProduct s κ).presheaf.stalk z) := pullback.snd _ _

/-- The full original endpoint of the localized chart. -/
def boundaryGenericEndpoint : boundaryGenericChart n o U e hU s κ Q ⟶ A :=
  pullback.fst π ι ≫ b

instance boundaryGenericProjection_finite :
    IsFinite (boundaryGenericProjection n o U e hU s κ Q) := by
  unfold boundaryGenericProjection
  infer_instance

instance boundaryGenericProjection_flat : Flat (boundaryGenericProjection n o U e hU s κ Q) := by
  unfold boundaryGenericProjection
  infer_instance

instance boundaryGenericProjection_surjective :
    Surjective (boundaryGenericProjection n o U e hU s κ Q) := by
  unfold boundaryGenericProjection
  infer_instance

instance boundaryGenericChart_affine : IsAffine (boundaryGenericChart n o U e hU s κ Q) :=
  isAffine_of_isAffineHom (boundaryGenericProjection n o U e hU s κ Q)

/-- The localized chart is an effective cover of the full original generic local scheme. -/
instance boundaryGenericProjection_effectiveEpi :
    EffectiveEpi (boundaryGenericProjection n o U e hU s κ Q) := by infer_instance

/-- All original local chart points have the component's constructed exact rank. -/
theorem boundaryGenericEndpoint_exactRank :
    Set.range (boundaryGenericEndpoint n o U e hU s κ Q) ⊆ exactRank (Over.mk p) m := by
  rintro _ ⟨y, rfl⟩
  have hc := congrArg (fun f ↦ f y) (pullback.condition (f := π) (g := ι))
  change π (pullback.fst π ι y) = ι (pullback.snd π ι y) at hc
  rw [boundaryComponentPoint_fromSpecStalk] at hc
  have h : π (pullback.fst π ι y) ∈ boundaryExactRank n o U e hU s κ m := by
    rw [hc]
    exact boundaryPointRank_spec n o U e hU s κ z
  change pullback.fst π ι y ∈ π ⁻¹' boundaryExactRank n o U e hU s κ m at h
  rw [boundaryExactRank_preimage] at h
  exact h

/-- The constructed local rank remains at least the size of the original retained frame. -/
theorem boundaryGeneric_rank_ge : n ≤ m :=
  boundaryExactRank_ge n o U e hU s κ m z (boundaryPointRank_spec n o U e hU s κ z)

/-- Complete frames cover the entire generic local chart at its actual constructed rank. -/
theorem boundaryGeneric_complete_frame_surjective :
    Function.Surjective (rankFrameProjection (Over.mk p) m
      (boundaryGenericEndpoint n o U e hU s κ Q)) :=
  rankFrameProjection_surjective (Over.mk p) m _
    (boundaryGenericEndpoint_exactRank n o U e hU s κ Q)

/-- Complete frames split the full original relation over every generic local component chart. -/
def boundaryGenericSplitIso :
    (∐ fun _ : Fin m ↦ rankFrameCover (Over.mk p) m
      (boundaryGenericEndpoint n o U e hU s κ Q)) ≅
    pullback p (rankFrameProjection (Over.mk p) m
      (boundaryGenericEndpoint n o U e hU s κ Q) ≫
        boundaryGenericEndpoint n o U e hU s κ Q) :=
  rankFrameCoverIso (Over.mk p) m (boundaryGenericEndpoint n o U e hU s κ Q)
    (boundaryGenericEndpoint_exactRank n o U e hU s κ Q)

variable [AlgebraicGeometry.IsNoetherian A]

/-- A finite original rank order recovers the full local chart, without reducing its local ring. -/
theorem boundaryGeneric_rank_recovery :
    ∃ k : ℕ, IsIso (rankPullbackMap (Over.mk p)
      (boundaryGenericEndpoint n o U e hU s κ Q) m k) :=
  exists_rankPullbackMap_isIso (Over.mk p) (boundaryGenericEndpoint n o U e hU s κ Q) m
    (boundaryGenericEndpoint_exactRank n o U e hU s κ Q)

end FLT.Mazur.EquivalenceRelationNormalizedFrames
