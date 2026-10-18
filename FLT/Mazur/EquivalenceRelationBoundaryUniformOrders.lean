/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationChartRankStageIdeal
public import FLT.Mazur.SchemeFiniteGroupBoundaryTestIdeal
public import FLT.Mazur.EquivalenceRelationBoundaryRankThickenings

/-!
# Uniform original rank orders on every scalar boundary product

The comparison constants depend only on the original chart. They work for
every scalar ring and every boundary coefficient ring, with their full ideals
and nilpotents intact. No coverage or nilpotence of those ideals is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
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
  [IsAffine U.toScheme] [IsNoetherian U.toScheme]
local instance uniformBoundaryOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance uniformBoundaryOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local notation "ρ" => restrictedAction (action e (Fin n) o) U hU
local notation "tests" => completeAffineOrbitTests e (Fin n) o U hU
local notation "Z" => U.ι ⁻¹' completePointLocus (p := p) (q := q) (Fin n) o
variable {R T : Type} [CommRing R] [CommRing T]
  (s : R →+* invariantCoordinates (restrictedAction (action e (Fin n) o) U hU)) (κ : R →+* T)

/-- The full scalar chart is affine even when the original boundary coefficients are arbitrary. -/
instance chartBoundary_affine : IsAffine (chartBoundary n o U e hU s κ) := by
  unfold chartBoundary
  infer_instance

attribute [local irreducible] chartBoundary chartBoundaryChart chartBoundaryProduct
  chartBoundaryEndpoint

omit [QuasiCompact p] in
/-- Test ideals coincide scheme-theoretically on the original full scalar chart. -/
theorem chartBoundary_test_sheaf :
    (boundaryTestSheaf s κ tests).comap (chartBoundaryProduct n o U e hU s κ) =
      (orbitTestChartIdeal ρ Z (completeChart_isClosed (Fin n) o U)).comap
        (chartBoundaryChart n o U e hU s κ) := by
  exact boundary_test_sheaf_eq ρ Z (completeChart_isClosed (Fin n) o U) s κ
    (chartBoundaryChart n o U e hU s κ) (chartBoundaryProduct n o U e hU s κ)
    (by
      unfold chartBoundaryChart chartBoundaryProduct chartBoundary
      exact pullback.condition (f := quotientMap ρ) (g := boundaryProjection s κ))

/-- One pair of original-chart bounds controls every scalar boundary and every finite rank order. -/
theorem boundary_rank_test_uniform_orders :
    ∃ c d : ℕ, 0 < c ∧ 0 < d ∧
      ∀ (R T : Type) [CommRing R] [CommRing T]
        (s : R →+* invariantCoordinates (restrictedAction (action e (Fin n) o) U hU))
        (κ : R →+* T) (k : ℕ),
        (rankPullbackMap (Over.mk p) (chartBoundaryEndpoint n o U e hU s κ) n k).ker ^ c ≤
          (boundaryTestSheaf s κ tests).comap (chartBoundaryProduct n o U e hU s κ) ^
            (k + 1) ∧
        (boundaryTestSheaf s κ tests).comap (chartBoundaryProduct n o U e hU s κ) ^
            (d * (k + 1)) ≤
          (rankPullbackMap (Over.mk p) (chartBoundaryEndpoint n o U e hU s κ) n k).ker := by
  obtain ⟨c, d, hc, hd, h⟩ := chartRankStage_uniform_kernel_bounds n o U e hU
  refine ⟨c, d, hc, hd, ?_⟩
  intro R T _ _ s κ k
  rw [chartBoundary_test_sheaf, chartBoundaryEndpoint]
  exact h _ (chartBoundaryChart n o U e hU s κ) k


/-- A proved test-power equation supplies an explicit finite order recovering the full chart. -/
theorem boundary_rank_recovery_uniform_order :
    ∃ c : ℕ, 0 < c ∧ ∀ k : ℕ,
      (boundaryTestSheaf s κ tests).comap (chartBoundaryProduct n o U e hU s κ) ^
          (k + 1) = ⊥ →
        IsIso (rankPullbackMap (Over.mk p) (chartBoundaryEndpoint n o U e hU s κ)
          n (c * (k + 1) - 1)) := by
  obtain ⟨c, d, hc, _, h⟩ := boundary_rank_test_uniform_orders n o U e hU
  refine ⟨c, hc, fun k hk ↦ ?_⟩
  have hb := (h R T s κ k).1
  rw [hk] at hb
  unfold chartBoundaryEndpoint at hb ⊢
  change IsIso (rankPullbackMap (Over.mk p)
    (chartBoundaryChart n o U e hU s κ ≫ U.ι ≫ first p q (Fin n) o)
    n (c * (k + 1) - 1))
  apply IsClosedImmersion.isIso_iff_ker_eq_bot.mpr
  rw [chartRankStage_kernel, Nat.sub_add_cancel (Nat.mul_pos hc (Nat.succ_pos k))]
  change (rankPullbackMap (Over.mk p)
    (chartBoundaryChart n o U e hU s κ ≫ U.ι ≫ first p q (Fin n) o) n k).ker ^ c ≤ ⊥ at hb
  rw [chartRankStage_kernel, ← pow_mul, Nat.mul_comm (k + 1) c] at hb
  exact bot_unique hb

/-- Recovery at a known rank order supplies an explicit original chart test-power equation. -/
theorem boundary_test_power_of_rank_recovery :
    ∃ d : ℕ, 0 < d ∧ ∀ k : ℕ,
      IsIso (rankPullbackMap (Over.mk p) (chartBoundaryEndpoint n o U e hU s κ) n k) →
        (boundaryTestSheaf s κ tests).comap (chartBoundaryProduct n o U e hU s κ) ^
          (d * (k + 1)) = ⊥ := by
  obtain ⟨c, d, _, hd, h⟩ := boundary_rank_test_uniform_orders n o U e hU
  refine ⟨d, hd, fun k hk ↦ ?_⟩
  let _ := hk
  have hb := (h R T s κ k).2
  rw [Scheme.Hom.ker_eq_bot_of_isIso] at hb
  exact bot_unique hb


/-- Equations in the full original product give the same explicit chart recovery order. -/
theorem boundary_rank_recovery_of_product_power :
    ∃ c : ℕ, 0 < c ∧ ∀ k : ℕ,
      boundaryTestIdeal s κ tests ^ (k + 1) = ⊥ →
        IsIso (rankPullbackMap (Over.mk p) (chartBoundaryEndpoint n o U e hU s κ)
          n (c * (k + 1) - 1)) := by
  obtain ⟨c, hc, h⟩ := boundary_rank_recovery_uniform_order n o U e hU s κ
  refine ⟨c, hc, fun k hk ↦ h k ?_⟩
  have hj : boundaryTestSheaf s κ tests ^ (k + 1) = ⊥ := by
    apply bot_unique
    apply Scheme.IdealSheafData.le_of_isAffine
    simp only [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply, boundaryTestSheaf,
      Scheme.IdealSheafData.ofIdealTop_ideal, homOfLE_refl, op_id]
    rw [(boundaryProduct s κ).presheaf.map_id]
    simpa only [CommRingCat.hom_id, Ideal.map_id, Scheme.IdealSheafData.ideal_bot, Pi.bot_apply]
      using hk.le
  rw [← IdealSheafPowerPullback.comap_pow, hj, Scheme.IdealSheafData.comap_bot]

end FLT.Mazur.EquivalenceRelationNormalizedFrames
