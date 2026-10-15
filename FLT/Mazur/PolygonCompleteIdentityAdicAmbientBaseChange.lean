/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.MonoBaseChangeRelation
public import FLT.Mazur.PolygonCompleteIdentityAdicAmbientStructure

/-!
# The full original adic lifting space is the actual coefficient base change

Both original projections are retained. Their relation over the original
cubic is the base change of the complete relation, before taking its graph.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonInfinitesimal
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (m : ℕ)
local notation "S" => Spec (CommRingCat.of (PowerSeries K))
local notation "a" => completeIdentityActionTarget K n h 0
local notation "g" => completePointToIntegralCubic K n h 0
local notation "f" => completeIdentityFiniteInput K n h 0 m
local notation "r" => originalStageToCompatibleProj K n h m
local notation "π" => exactVeroneseProjToBase K n h
local notation "w" => WeierstrassIntegralChart.integralCurveStructure
  (completePointWeierstrassCurve K n h 0) ≫ inv (Scheme.toSpecΓ (S))
local notation "s" => scalingParameterProjection (Ring K m) (parameter K m) n h ≫
  (CategoryTheory.Over.hom (family K m n h))

/-- The actual adic relation has the original finite source coefficient morphism. -/
def completeIdentityAdicLiftSpaceStructure :
    completeIdentityActionAdicLiftSpace K n h m ⟶ Spec (.of (Ring K m)) :=
  pullback.fst _ _ ≫ (s)

/-- No extra ambient equations arise from separately base-changing the two original inputs. -/
theorem completeIdentityAdicLiftSpace_isPullback :
    IsPullback (completeIdentityActionAdicLiftSpaceMap K n h m)
      (completeIdentityAdicLiftSpaceStructure K n h m)
      (completeIdentityActionLiftSpaceStructure K n h) (baseToSeries K m) := by
  have ha : (a) ≫ (w) = completeIdentityActionSecond K n h ≫ (π) := by
    rw [completeIdentityActionTarget_structure_assoc,
      IsIso.hom_inv_id, Category.comp_id]
  have hg : (g) ≫ (w) = (π) := by
    rw [completePointToIntegralCubic_over_assoc,
      IsIso.hom_inv_id, Category.comp_id]
  have hx : IsPullback (f) (s) ((a) ≫ (w)) (baseToSeries K m) := by
    rw [ha]
    exact completeIdentityFiniteInput_base_isPullback K n h 0 m
  have hy : IsPullback (r) (family K m n h).hom ((g) ≫ (w)) (baseToSeries K m) := by
    rw [hg]
    exact originalStageToCompatibleProj_isPullback K n h m
  have hp := MonoBaseChangeRelation.isPullback (a) (g) (w) (baseToSeries K m)
    (f) (s) (r) (family K m n h).hom hx hy
  rw [ha] at hp
  exact hp

end FLT.Mazur.PolygonInfinitesimalStages
