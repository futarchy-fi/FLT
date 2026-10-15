/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFiniteLawComparison
public import FLT.Mazur.PolygonCompleteIdentityActionRotatedMultiplication
public import FLT.Mazur.PolygonCompleteStageRotation

/-!
# Every finite edge retains the same original identity multiplication

The original rotations identify all full finite Laurent edges with the
zero-labeled edge. Their actual cubic action targets are the same original
identity multiplication followed by the corresponding original rotation.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonInfinitesimal PolygonSmoothing PolygonPinching
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
  completeRotation
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (m : ℕ) (b : ZMod n)
local notation "A" => Ring K m
local notation "t" => parameter K m
local notation "G" => completePointOriginalBaseGroup K n h (0 : Fin n)
local notation "U" => completePointIdentityOpen K n h (0 : Fin n)
local notation "π" => exactVeroneseProjToBase K n h
local notation "p" => originalStageToCompatibleProj K n h m
local notation "e" => completeIdentityStageTorus K n h 0 m
local notation "q" => completeIdentityFiniteInput K n h 0 m
local notation "j" => edge (A)[T;T⁻¹] (LaurentPolynomial.C (t)) n h (rotateIndex b 0)
local notation "r" => Spec.map (CommRingCat.ofHom (PolygonScalingNaturality.coeffMap
  (LaurentPolynomial.C : (A) →+* (A)[T;T⁻¹])))

/-- The original zero finite edge rotates to each original labeled finite edge. -/
@[reassoc] theorem completeIdentityStageEdge_rotation :
    (e) ≫ (U).ι ≫ completeRotation K n h b =
      edge (A) (t) n h (rotateIndex b 0) ≫ (p) := by
  rw [completeIdentityStageTorus_inclusion_assoc, originalStageToCompatibleProj_rotation]
  change edge (A) (t) n h 0 ≫ rotation (A) (t) n h b ≫ (p) = _
  rw [edge, Category.assoc, chart_rotation_assoc, edge, Category.assoc]

/-- The exact finite input on any full edge is the original pair with its second input rotated. -/
@[reassoc] theorem completeIdentityFinitePair_rotatedInput :
    completeIdentityFinitePair K n h 0 m ≫ completeIdentityRotatedPairToAction K n h b =
      (j) ≫ (q) := by
  apply pullback.hom_ext
  · rw [Category.assoc, completeIdentityRotatedPairToAction_fst,
      completeIdentityFinitePair_fst, Category.assoc, completeIdentityFiniteInput_fst,
      edge_toBase_assoc]
  · rw [Category.assoc, completeIdentityRotatedPairToAction_snd,
      completeIdentityFinitePair_snd_assoc, completeIdentityStageEdge_rotation,
      Category.assoc, completeIdentityFiniteInput_snd]
    have he := (edge_parameter_isPullback (t) n h
      (LaurentPolynomial.C : (A) →+* (A)[T;T⁻¹])
      (LaurentPolynomial.C (t)) rfl (rotateIndex b 0)).w
    change (r) ≫ edge (A) (t) n h (rotateIndex b 0) =
      (j) ≫ scalingParameterProjection (A) (t) n h at he
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ (p)) he).trans (Category.assoc _ _ _))

/-- Every full finite edge's cubic target is the same actual original identity multiplication. -/
@[reassoc] theorem completeIdentityFiniteOriginalMul_rotatedCubic :
    completeIdentityFiniteOriginalMul K n h 0 m ≫ (U).ι ≫ completeRotation K n h b ≫
        completePointToIntegralCubic K n h 0 =
      (j) ≫ (q) ≫ completeIdentityActionTarget K n h 0 := by
  rw [completeIdentityFiniteOriginalMul, Category.assoc,
    ← completeIdentityRotatedPairToAction_target, completeIdentityFinitePair_rotatedInput_assoc]

/-- Every full finite edge's constructed polygon map is the same literal Laurent scaling. -/
@[reassoc] theorem completeIdentityFiniteScaling_rotatedEdge :
    (j) ≫ completeIdentityFiniteScaling K n h m =
      universalEdgeScaling (A) ≫ (e) ≫ (U).ι ≫ completeRotation K n h b := by
  rw [completeIdentityFiniteScaling, edge_universalScaling_assoc,
    completeIdentityStageEdge_rotation]

end FLT.Mazur.PolygonInfinitesimalStages
