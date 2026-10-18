/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeExactRankFinite
public import FLT.Mazur.RelativeRankPullbackThickenings
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Finite original sources on every residual rank thickening

Finiteness holds on the unsplit stages with their actual ideal-power structure.
Over a locally Noetherian original base the stage maps are finitely presented.
A stage meeting the residual nonfinite locus of a coefficient scheme cannot
be flat over that scheme; pointwise rank coverage alone is not flat descent.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.RelativeOrderedTuples
open SchemeOpenEnvelope
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S B : Scheme.{0}} (E : Over S) [Etale E.hom] [IsSeparated E.hom]
  [QuasiCompact E.hom] (b : B ⟶ S) (n k : ℕ)

instance rankThickeningMap_locallyOfFiniteType :
    LocallyOfFiniteType (rankThickeningMap E n k) := by
  unfold rankThickeningMap
  infer_instance

instance rankThickeningMap_locallyOfFinitePresentation [IsLocallyNoetherian S] :
    LocallyOfFinitePresentation (rankThickeningMap E n k) := inferInstance

instance rankPullbackMap_locallyOfFinitePresentation [IsLocallyNoetherian S] :
    LocallyOfFinitePresentation (rankPullbackMap E b n k) := by
  unfold rankPullbackMap
  infer_instance

variable [LocallyQuasiFinite E.hom]

/-- The entire original source is finite on each actual ideal-power rank stratum. -/
theorem finite_pullback_rankThickening :
    IsFinite (pullback.snd E.hom (rankThickeningMap E n k)) :=
  finite_pullback_of_exactRank E n _ (rankThickeningMap_range E n k).le

/-- Arbitrary coefficients preserve finiteness on every unsplit rank stage. -/
theorem finite_pullback_rankPullback :
    IsFinite (pullback.snd E.hom (rankPullbackMap E b n k ≫ b)) := by
  apply finite_pullback_of_exactRank E n
  rintro _ ⟨x, rfl⟩
  exact rankPullback_endpoint E b n k x

/-- The finite projection is also a base change of the original coefficient source. -/
theorem finite_iterated_pullback_rankPullback :
    IsFinite (pullback.snd (pullback.snd E.hom b) (rankPullbackMap E b n k)) := by
  let _ := finite_pullback_rankPullback E b n k
  rw [← pullbackLeftPullbackSndIso_hom_snd E.hom b (rankPullbackMap E b n k)]
  infer_instance

/-- A residual rank stage cannot be used as a flat descent cover of the coefficient scheme. -/
theorem rankPullbackMap_not_flat [IsLocallyNoetherian S]
    (x : rankPullbackThickening E b n k)
    (hx : rankPullbackMap E b n k x ∉ finiteTargetOpen (pullback.snd E.hom b)) :
    ¬ Flat (rankPullbackMap E b n k) := by
  intro h
  let _ := h
  let _ := finite_iterated_pullback_rankPullback E b n k
  apply hx
  apply (mem_finiteTargetOpen_fppf_iff
    (IsPullback.of_hasPullback (pullback.snd E.hom b) (rankPullbackMap E b n k)) x).mp
  rw [finiteTargetOpen_eq_top]
  trivial

/-- The same obstruction already occurs on the original residual stratum. -/
theorem rankThickeningMap_not_flat [IsLocallyNoetherian S]
    (x : rankThickening E n k) (hx : rankThickeningMap E n k x ∉ finiteTargetOpen E.hom) :
    ¬ Flat (rankThickeningMap E n k) :=
  exactRank_not_flat_at_residual E n _ (rankThickeningMap_range E n k).le x hx

end FLT.Mazur.RelativeOrderedTuples
