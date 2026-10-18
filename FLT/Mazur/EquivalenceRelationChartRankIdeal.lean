/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationBoundaryComponentRank
public import FLT.Mazur.RelativeRankStratumThickenings
public import FLT.Mazur.SchemeFiniteGroupTestAdicComparison

/-!
# The original rank ideal on a normalized frame chart

The distinguished frame factors the chart endpoint through the original rank
image open. Pulling back the original rank ideal produces an actual ideal
sheaf whose support is exactly the complete chart locus.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] source
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (n : ℕ) (o : Fin n) (U : (source p q (Fin n) o).Opens)
local instance chartRankIdealOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance chartRankIdealOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›

/-- Every original chart endpoint lies in the actual n-frame image open. -/
theorem chartEndpoint_range_rankImage :
    Set.range (U.ι ≫ first p q (Fin n) o) ⊆ Set.range (rankImageOpen (Over.mk p) n).ι := by
  rw [Scheme.Opens.range_ι]
  rintro _ ⟨x, rfl⟩
  exact ⟨inclusion p q (Fin n) o (U.ι x), rfl⟩

/-- Factor through the original rank open without reducing the chart. -/
def chartRankOpenLift : U.toScheme ⟶ (rankImageOpen (Over.mk p) n).toScheme :=
  IsOpenImmersion.lift (rankImageOpen (Over.mk p) n).ι
    (U.ι ≫ first p q (Fin n) o) (chartEndpoint_range_rankImage n o U)

/-- The lift retains the entire original endpoint map. -/
@[reassoc]
theorem chartRankOpenLift_endpoint :
    chartRankOpenLift n o U ≫ (rankImageOpen (Over.mk p) n).ι =
      U.ι ≫ first p q (Fin n) o := IsOpenImmersion.lift_fac _ _ _

/-- The actual original rank ideal restricted to the unchanged normalized chart. -/
def chartRankIdeal : U.toScheme.IdealSheafData :=
  (rankStratumIdeal (Over.mk p) n).comap (chartRankOpenLift n o U)

variable [QuasiCompact p]

/-- The original rank equations cut out all and only the complete original chart points. -/
theorem chartRankIdeal_support :
    (chartRankIdeal n o U).support =
      ⟨U.ι ⁻¹' completePointLocus (p := p) (q := q) (Fin n) o,
        completeChart_isClosed (Fin n) o U⟩ := by
  rw [chartRankIdeal, Scheme.IdealSheafData.support_comap]
  ext x
  change (rankImageOpen (Over.mk p) n).ι (chartRankOpenLift n o U x) ∈
    rankAtMost (Over.mk p) n ↔ _
  have he := congrArg (fun f ↦ f x) (chartRankOpenLift_endpoint n o U)
  change (rankImageOpen (Over.mk p) n).ι (chartRankOpenLift n o U x) =
    first p q (Fin n) o (U.ι x) at he
  rw [he]
  have hn : first p q (Fin n) o (U.ι x) ∈ rankImageOpen (Over.mk p) n :=
    ⟨inclusion p q (Fin n) o (U.ι x), rfl⟩
  exact ⟨fun h ↦ (chart_complete_iff_exactRank n o U x).mpr ⟨hn, h⟩,
    fun h ↦ ((chart_complete_iff_exactRank n o U x).mp h).2⟩


open FiniteGroupRestriction SchemeFiniteGroupQuotient
variable (e : CategoryTheory.EquivalenceRelation p q)
  (hU : ∀ g : Equiv.Perm (Fin n), (action e (Fin n) o g).hom ⁻¹ᵁ U = U)
  [IsAffine U.toScheme] [IsNoetherian U.toScheme]
local notation "ρ" => restrictedAction (action e (Fin n) o) U hU
local notation "Z" => U.ι ⁻¹' completePointLocus (p := p) (q := q) (Fin n) o
local notation "J" => orbitTestChartIdeal ρ Z (completeChart_isClosed (Fin n) o U)

/-- The original rank and test ideals have linear comparison bounds before scalar base change. -/
theorem chartRank_test_uniform_comparison :
    ∃ c d : ℕ, 0 < c ∧ 0 < d ∧
      ∀ (Y : Scheme.{0}) (f : Y ⟶ U.toScheme) (k : ℕ),
        (chartRankIdeal n o U).comap f ^ (c * k) ≤ (J).comap f ^ k ∧
          (J).comap f ^ (d * k) ≤ (chartRankIdeal n o U).comap f ^ k := by
  apply AffineUniformIdealPowers.exists_uniform_comap_comparison
  rw [chartRankIdeal_support,
    orbitTestChartIdeal_support ρ Z (completeChart_isClosed (Fin n) o U)
      (completeChart_stable e (Fin n) o U hU)]

end FLT.Mazur.EquivalenceRelationNormalizedFrames
