/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFirstQuotientLocalErrors
public import FLT.Mazur.PolygonCompleteIdentityFirstAmbientNodeGenerators
public import FLT.Mazur.PolygonCompleteIdentityFirstSourceNodeCoverage
public import FLT.Mazur.PolygonCompleteIdentityFirstChartAmbientSocle
public import FLT.Mazur.TwoCoordinateLocalSocle

/-!
# Original ambient socle representatives belong to the smaller ideal on every patch

The full node kernel has two actual error generators modulo the parameter.
Their local vanishing at source-node primes, together with the original
coordinate annihilators away from that locus, detects full ideal membership.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
  completeIdentityActionAdicChartSpaceMap completeIdentityActionAdicLiftSpaceMap
  FCurve.ModuleSheafTensor.tensor FCurve.divisorLineBundle
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
variable (U : (completeIdentityActionAdicChartAmbientOpen K n h 1 0 0).toScheme.affineOpens)
local notation "V" => completeIdentityAdicAmbientSourcePatch K n h 1 0 0 U
local notation "R" => completeIdentityActionAdicChartSpace K n h 1 0 0
local notation "f" => completeIdentityActionGraphAdicChartEmbedding K n h 1 0 0
local notation "M" => completeIdentityFirstSourcePolePatchMap K n h U
local notation "A" => Γ((R), (V).1)
local notation "ρ" => completeIdentityFirstAmbientRestriction K n h (V)
local notation "J" => completeIdentityFirstChartClosedAmbientIdeal K n h
local notation "I" => Ideal.map (CommRingCat.Hom.hom (ρ)) (J)
local notation "q" => Ideal.Quotient.mk (I)
local notation "s" => completeIdentityFirstPoleSource K n h U
local notation "t" => parameter K 1
local notation "e" => parameter K[T;T⁻¹] 1
local notation "a" => completeIdentityFirstAmbientSourceFunctions K n h
local notation "δ" => completeIdentityFirstAmbientError K n h
variable (z : Γ(completeIdentityActionAdicChartSpace K n h 1 0 0, ⊤))
variable (hx : completeIdentityFirstAmbientSourceFunctions K n h
  (leftCoordinate (parameter K[T;T⁻¹] 1)) * z ∈ completeIdentityFirstChartClosedAmbientIdeal K n h)
variable (hy : completeIdentityFirstAmbientSourceFunctions K n h
  (rightCoordinate (parameter K[T;T⁻¹] 1)) * z ∈ completeIdentityFirstChartClosedAmbientIdeal K n h)
include hx hy

/-- Every full ambient common annihilator belongs to the unchanged ideal on this affine patch. -/
theorem completeIdentityFirstLocalSocle_mem : (ρ) z ∈ (I) := by
  let ψ : Γ((R), ⊤) →+* (A) ⧸ (I) := (q).comp (ρ).hom
  have ht : ψ (completeIdentityFirstAmbientParameter K n h) = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [completeIdentityFirstChartClosedAmbientIdeal_restrict]
    exact Ideal.mem_sup_right (Ideal.subset_span (Set.mem_singleton _))
  have hn := completeIdentityFirstChartAmbientSocle_nodeKernel K n h z hx hy
  have hz : ψ z ∈ Ideal.span {ψ ((δ) (leftCoordinate (t))),
      ψ ((δ) (rightCoordinate (t)))} := by
    have hm : z ∈ Ideal.span {completeIdentityFirstAmbientParameter K n h} ⊔
        Ideal.span {(δ) (leftCoordinate (t)), (δ) (rightCoordinate (t))} := by
      rw [← completeIdentityFirstAmbientNodeKernel_twoCoordinates]
      exact hn
    have hm' := Ideal.mem_map_of_mem ψ hm
    simpa only [Ideal.map_sup, Ideal.map_span, Set.image_singleton, Set.image_insert_eq,
      ht, Ideal.span_singleton_zero, bot_sup_eq] using hm'
  have hl : (q) ((s) (leftCoordinate (t))) * ψ z = 0 := by
    change (q) ((s) (leftCoordinate (t))) * (q) ((ρ) z) = 0
    rw [← map_mul]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [completeIdentityFirstPoleSource_left, mul_assoc]
    apply Ideal.mul_mem_left
    change (ρ) ((a) (leftCoordinate (e))) * (ρ) z ∈ (I)
    rw [← map_mul]
    exact Ideal.mem_map_of_mem (ρ).hom hx
  have hr : (q) ((s) (rightCoordinate (t))) * ψ z = 0 := by
    change (q) ((s) (rightCoordinate (t))) * (q) ((ρ) z) = 0
    rw [← map_mul]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [completeIdentityFirstPoleSource_right, mul_assoc]
    apply Ideal.mul_mem_left
    change (ρ) ((a) (rightCoordinate (e))) * (ρ) z ∈ (I)
    rw [← map_mul]
    exact Ideal.mem_map_of_mem (ρ).hom hy
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  apply TwoCoordinateLocalSocle.eq_zero _ _ _ (ψ z) hz hl hr
  intro p hp hq
  obtain ⟨he₁, he₂⟩ := completeIdentityFirstQuotientLocal_errors_zero K n h U p hp hq
  change Ideal.span {ψ ((δ) (leftCoordinate (t))), ψ ((δ) (rightCoordinate (t)))} ≤
    RingHom.ker (algebraMap ((A) ⧸ (I)) (Localization.AtPrime p.asIdeal))
  rw [Ideal.span_le]
  intro v hv
  rcases Set.mem_insert_iff.mp hv with rfl | hv
  · exact he₁
  · rw [Set.mem_singleton_iff] at hv
    subst v
    exact he₂

end FLT.Mazur.PolygonInfinitesimalStages
