/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationChartRankIdeal
public import FLT.Mazur.RelativeRankPullbackThickenings
public import FLT.Mazur.IdealSheafPowerPullback
public import FLT.Mazur.SchemeMonoIdealPullback

/-!
# Exact kernels of the original matching rank stages

On every coefficient scheme over the original normalized chart, the matching
rank stage is a closed immersion with the computed ideal-power kernel. The
comparison with invariant tests therefore controls actual original stages.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open RelativeOrderedTuples FiniteGroupRestriction SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] source
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (n : ℕ) (o : Fin n) (U : (source p q (Fin n) o).Opens)
local instance chartRankStageOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance chartRankStageOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
variable {Y : Scheme.{0}} (f : Y ⟶ U.toScheme) (k : ℕ)
local notation "b" => f ≫ U.ι ≫ first p q (Fin n) o

/-- The matching original rank stage is closed on every coefficient scheme over the chart. -/
instance chartRankStage_closed :
    IsClosedImmersion (rankPullbackMap (Over.mk p) b n k) := by
  change IsClosedImmersion (pullback.snd
    ((rankStratumIdeal (Over.mk p) n ^ (k + 1)).subschemeι ≫
      (rankImageOpen (Over.mk p) n).ι) b)
  rw [← chartRankOpenLift_endpoint n o U, ← Category.assoc]
  infer_instance

/-- The complete ideal-power kernel is independent of any reduced-support replacement. -/
theorem chartRankStage_kernel :
    (rankPullbackMap (Over.mk p) b n k).ker =
      (chartRankIdeal n o U).comap f ^ (k + 1) := by
  change (pullback.snd
    ((rankStratumIdeal (Over.mk p) n ^ (k + 1)).subschemeι ≫
      (rankImageOpen (Over.mk p) n).ι) b).ker = _
  rw [← chartRankOpenLift_endpoint n o U, ← Category.assoc,
    SchemeMonoIdealPullback.idealPullback_snd_kernel, IdealSheafPowerPullback.comap_pow,
    Scheme.IdealSheafData.comap_comp]
  rfl

variable [QuasiCompact p] (e : CategoryTheory.EquivalenceRelation p q)
  (hU : ∀ g : Equiv.Perm (Fin n), (action e (Fin n) o g).hom ⁻¹ᵁ U = U)
  [IsAffine U.toScheme] [IsNoetherian U.toScheme]
local notation "ρ" => restrictedAction (action e (Fin n) o) U hU
local notation "Z" => U.ι ⁻¹' completePointLocus (p := p) (q := q) (Fin n) o
local notation "J" => orbitTestChartIdeal ρ Z (completeChart_isClosed (Fin n) o U)

/-- Uniform original test bounds apply to the kernels of the existing actual rank stages. -/
theorem chartRankStage_uniform_kernel_bounds :
    ∃ c d : ℕ, 0 < c ∧ 0 < d ∧
      ∀ (Y : Scheme.{0}) (f : Y ⟶ U.toScheme) (k : ℕ),
        (rankPullbackMap (Over.mk p) (f ≫ U.ι ≫ first p q (Fin n) o) n k).ker ^ c ≤
          (J).comap f ^ (k + 1) ∧
        (J).comap f ^ (d * (k + 1)) ≤
          (rankPullbackMap (Over.mk p) (f ≫ U.ι ≫ first p q (Fin n) o) n k).ker := by
  obtain ⟨c, d, hc, hd, h⟩ := chartRank_test_uniform_comparison n o U e hU
  refine ⟨c, d, hc, hd, fun Y f k ↦ ?_⟩
  rw [chartRankStage_kernel, ← pow_mul, Nat.mul_comm (k + 1) c]
  exact h Y f (k + 1)

end FLT.Mazur.EquivalenceRelationNormalizedFrames
