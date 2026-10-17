/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityTopLocalAffineErrors
public import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Exact local error vanishing in the smaller graph-plus-parameter quotient

Only the original graph ideal and smoothing parameter are imposed.
At every source-node prime, the two errors vanish in the localization of
this full quotient, including all its nilpotents and embedded components.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
  completeIdentityActionAdicChartSpaceMap completeIdentityActionAdicLiftSpaceMap
  FCurve.ModuleSheafTensor.tensor FCurve.divisorLineBundle
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (m : ℕ)
variable (U : (completeIdentityActionAdicChartAmbientOpen K n h (m + 1) 0 0).toScheme.affineOpens)
local notation "V" => completeIdentityAdicAmbientSourcePatch K n h (m + 1) 0 0 U
local notation "R" => completeIdentityActionAdicChartSpace K n h (m + 1) 0 0
local notation "f" => completeIdentityActionGraphAdicChartEmbedding K n h (m + 1) 0 0
local notation "M" => completeIdentityTopSourcePolePatchMap K n h m U
local notation "A" => Γ((R), (V).1)
local notation "ρ" => completeIdentityTopAmbientRestriction K n h m (V)
local notation "J" => completeIdentityTopChartClosedAmbientIdeal K n h m
local notation "I" => Ideal.map (CommRingCat.Hom.hom (ρ)) (J)
local notation "q" => Ideal.Quotient.mk (I)
local notation "s" => completeIdentityTopPoleSource K n h m U
local notation "t" => parameter K (m + 1)
variable (p : PrimeSpectrum (Γ(completeIdentityActionAdicChartSpace K n h (m + 1) 0 0,
  (completeIdentityAdicAmbientSourcePatch K n h (m + 1) 0 0 U).1) ⧸
    Ideal.map (completeIdentityTopAmbientRestriction K n h m
      (completeIdentityAdicAmbientSourcePatch K n h (m + 1) 0 0 U)).hom
      (completeIdentityTopChartClosedAmbientIdeal K n h m)))
local notation "B" => Localization.AtPrime p.asIdeal
local notation "l" => algebraMap ((A) ⧸ (I)) (B)

/-- The actual smaller quotient has zero coordinate errors in every source-node local ring. -/
theorem completeIdentityTopQuotientLocal_errors_zero
    (hx : (q) ((s) (leftCoordinate (t))) ∈ p.asIdeal)
    (hy : (q) ((s) (rightCoordinate (t))) ∈ p.asIdeal) :
    (l) ((q) ((ρ) (completeIdentityTopAmbientError K n h m (leftCoordinate (t))))) = 0 ∧
      (l) ((q) ((ρ) (completeIdentityTopAmbientError K n h m (rightCoordinate (t))))) = 0 := by
  let ψ : (A) →+* (B) := (l).comp (q)
  have hI : (f).ker.ideal (V) ≤ RingHom.ker ψ := by
    intro z hz
    have hi : z ∈ (I) := by
      rw [completeIdentityTopChartClosedAmbientIdeal_restrict]
      exact Ideal.mem_sup_left hz
    change (l) ((q) z) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hi, map_zero]
  have ht : ψ ((ρ) (completeIdentityTopAmbientParameter K n h m)) = 0 := by
    have hi : (ρ) (completeIdentityTopAmbientParameter K n h m) ∈ (I) := by
      rw [completeIdentityTopChartClosedAmbientIdeal_restrict]
      exact Ideal.mem_sup_right (Ideal.subset_span (Set.mem_singleton _))
    change (l) ((q) _) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hi, map_zero]
  exact completeIdentityTopLocalTest_errors_zero K n h m U ψ
    ((IsLocalization.AtPrime.to_map_mem_maximal_iff (B) p.asIdeal _).mpr hx)
    ((IsLocalization.AtPrime.to_map_mem_maximal_iff (B) p.asIdeal _).mpr hy) hI ht

end FLT.Mazur.PolygonInfinitesimalStages
