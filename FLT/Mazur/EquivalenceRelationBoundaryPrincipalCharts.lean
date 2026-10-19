/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationBoundaryMatchingInterior
public import FLT.Mazur.RelativeRankStageRecovery

/-!
# Full principal charts around matching components

Power-annihilating denominators construct principal neighborhoods in the
unchanged product. Pulling back the original finite flat chart gives a
faithful chart of matching rank, recovering a finite original rank stage.
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
local instance principalChartOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance principalChartOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance principalChartOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
set_option quotPrecheck false
local notation "C" => Γ(boundaryProduct s κ, ⊤)
variable (u : Γ(boundaryProduct s κ, ⊤))
local notation "V" => (boundaryProduct s κ).basicOpen u

/-- The entire original chart pulled back to an actual principal coefficient neighborhood. -/
def boundaryPrincipalChart : Scheme := pullback π (V).ι

/-- The faithful projection to the full principal coefficient scheme. -/
def boundaryPrincipalProjection : boundaryPrincipalChart n o U e hU s κ u ⟶ (V).toScheme :=
  pullback.snd _ _

/-- The unchanged original endpoint over the principal neighborhood. -/
def boundaryPrincipalEndpoint : boundaryPrincipalChart n o U e hU s κ u ⟶ A :=
  pullback.fst π (V).ι ≫ b

instance boundaryPrincipalProjection_finite :
    IsFinite (boundaryPrincipalProjection n o U e hU s κ u) := by
  unfold boundaryPrincipalProjection
  infer_instance

instance boundaryPrincipalProjection_flat :
    Flat (boundaryPrincipalProjection n o U e hU s κ u) := by
  unfold boundaryPrincipalProjection
  infer_instance

instance boundaryPrincipalProjection_surjective :
    Surjective (boundaryPrincipalProjection n o U e hU s κ u) := by
  unfold boundaryPrincipalProjection
  infer_instance

instance boundaryPrincipalChart_affine : IsAffine (boundaryPrincipalChart n o U e hU s κ u) :=
  isAffine_of_isAffineHom (boundaryPrincipalProjection n o U e hU s κ u)

instance boundaryPrincipalProjection_effectiveEpi :
    EffectiveEpi (boundaryPrincipalProjection n o U e hU s κ u) := by infer_instance

variable [TopologicalSpace.NoetherianSpace U.toScheme]
local notation "tests" => completeAffineOrbitTests e (Fin n) o U hU
attribute [local irreducible] completeAffineOrbitTests boundaryTestIdeal
variable (order : ℕ)

/-- Every point of the original principal coefficient open has matching rank. -/
theorem boundaryPrincipal_point_exactRank
    (hu : u ∈ (boundaryTestIdeal s κ tests ^ order).annihilator) (x : (V).toScheme) :
    (V).ι x ∈ boundaryExactRank n o U e hU s κ n := by
  have hp : u ∉ ((boundaryProduct s κ).isoSpec.hom ((V).ι x)).asIdeal := by
    change (V).ι x ∈ (boundaryProduct s κ).toSpecΓ ⁻¹ᵁ PrimeSpectrum.basicOpen u
    rw [Scheme.toSpecΓ_preimage_basicOpen]
    exact x.property
  have hr := boundary_rank_eq_of_power_annihilator n o U e hU s κ order u hu ((V).ι x) hp
  exact (boundaryPointRank_eq_iff n o U e hU s κ ((V).ι x) n).mp hr

attribute [local irreducible] chartBoundary chartBoundaryProduct chartBoundaryEndpoint

/-- Every point of this full principal chart has exactly the retained original rank. -/
theorem boundaryPrincipalEndpoint_exactRank
    (hu : u ∈ (boundaryTestIdeal s κ tests ^ order).annihilator) :
    Set.range (boundaryPrincipalEndpoint n o U e hU s κ u) ⊆ exactRank (Over.mk p) n := by
  rintro _ ⟨y, rfl⟩
  have hc := congrArg (fun f ↦ f y) (pullback.condition (f := π) (g := (V).ι))
  change π (pullback.fst π (V).ι y) = (V).ι (pullback.snd π (V).ι y) at hc
  have he : π (pullback.fst π (V).ι y) ∈ boundaryExactRank n o U e hU s κ n := by
    rw [hc]
    exact boundaryPrincipal_point_exactRank n o U e hU s κ u order hu _
  change pullback.fst π (V).ι y ∈ π ⁻¹' boundaryExactRank n o U e hU s κ n at he
  rw [boundaryExactRank_preimage] at he
  exact he

/-- Complete frames cover the full coefficient neighborhood with its nilpotents unchanged. -/
theorem boundaryPrincipal_complete_frame_surjective
    (hu : u ∈ (boundaryTestIdeal s κ tests ^ order).annihilator) :
    Function.Surjective (rankFrameProjection (Over.mk p) n
      (boundaryPrincipalEndpoint n o U e hU s κ u)) :=
  rankFrameProjection_surjective (Over.mk p) n _
    (boundaryPrincipalEndpoint_exactRank n o U e hU s κ u order hu)

/-- Complete frames split the whole original relation over the actual principal chart. -/
def boundaryPrincipalSplitIso
    (hu : u ∈ (boundaryTestIdeal s κ tests ^ order).annihilator) :
    (∐ fun _ : Fin n ↦ rankFrameCover (Over.mk p) n
      (boundaryPrincipalEndpoint n o U e hU s κ u)) ≅
    pullback p (rankFrameProjection (Over.mk p) n
      (boundaryPrincipalEndpoint n o U e hU s κ u) ≫
        boundaryPrincipalEndpoint n o U e hU s κ u) :=
  rankFrameCoverIso (Over.mk p) n (boundaryPrincipalEndpoint n o U e hU s κ u)
    (boundaryPrincipalEndpoint_exactRank n o U e hU s κ u order hu)

variable [AlgebraicGeometry.IsNoetherian A]

/-- A finite matching stage recovers this entire principal chart as a scheme. -/
theorem boundaryPrincipal_rank_recovery
    (hu : u ∈ (boundaryTestIdeal s κ tests ^ order).annihilator) :
    ∃ k : ℕ, IsIso (rankPullbackMap (Over.mk p)
      (boundaryPrincipalEndpoint n o U e hU s κ u) n k) :=
  exists_rankPullbackMap_isIso (Over.mk p) (boundaryPrincipalEndpoint n o U e hU s κ u) n
    (boundaryPrincipalEndpoint_exactRank n o U e hU s κ u order hu)

end FLT.Mazur.EquivalenceRelationNormalizedFrames
