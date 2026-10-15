/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityGraphAdicInput
public import FLT.Mazur.PolygonCompleteIdentityGraphAdicLift

/-!
# Both original adic graph coordinates retain the same universal parameter

Lift the actual graph target into the original variable-parameter polygon,
using the unchanged parameter of the source. This constructs two original
polygon coordinates over the same full Laurent coefficient ring, without
specializing the unit or assuming preservation of a target node chart.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonInfinitesimal
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (m : ℕ)
local notation "A" => Ring K m
local notation "t" => parameter K m
local notation "q" => toBase (A)[T;T⁻¹] (LaurentPolynomial.C (t)) n h
local notation "r" => scalingParameterProjection (A) (t) n h
local notation "p" => completeIdentityActionGraphStageOriginalProjection K n h m
local notation "l" => completeIdentityActionGraphStageOriginalLift K n h m
local notation "b" => Spec.map (CommRingCat.ofHom (LaurentPolynomial.C : (A) →+* (A)[T;T⁻¹]))

/-- The original input projection retains the literal truncated coefficient map. -/
@[reassoc] theorem completeIdentityActionGraphStageOriginalProjection_structure :
    (p) ≫ (r) ≫ (family K m n h).hom =
      completeIdentityActionGraphStageStructure K n h m := by
  rw [completeIdentityActionGraphStageOriginalProjection, Category.assoc,
    ← completeIdentityActionInputStageOriginalIso_structure, Iso.inv_hom_id_assoc]
  rfl

/-- Source and original target have the same actual coefficient parameter. -/
theorem completeIdentityActionGraphStageParameter_square :
    (l) ≫ (family K m n h).hom = ((p) ≫ (q)) ≫ (b) := by
  rw [completeIdentityActionGraphStageOriginalLift_structure, Category.assoc,
    ← completeIdentityActionGraphStageOriginalProjection_structure]
  congr 1
  exact parameterProjection_base LaurentPolynomial.C (t) (LaurentPolynomial.C (t)) rfl n h

/-- The target in the original variable-parameter polygon, retaining the whole source unit. -/
def completeIdentityActionGraphStageParameterizedTarget :
    completeIdentityActionGraphStage K n h m ⟶ scalingParameterFamily (A) (t) n h :=
  (parameterProjection_isPullback LaurentPolynomial.C (t) (LaurentPolynomial.C (t)) rfl n h).lift
    (l) ((p) ≫ (q)) (completeIdentityActionGraphStageParameter_square K n h m)

/-- Forgetting only the variable parameter recovers the original-stage target exactly. -/
@[reassoc] theorem completeIdentityActionGraphStageParameterizedTarget_projection :
    completeIdentityActionGraphStageParameterizedTarget K n h m ≫ (r) = (l) :=
  IsPullback.lift_fst _ _ _ _

/-- The constructed target uses the same entire Laurent parameter as its original source. -/
@[reassoc] theorem completeIdentityActionGraphStageParameterizedTarget_parameter :
    completeIdentityActionGraphStageParameterizedTarget K n h m ≫ (q) = (p) ≫ (q) :=
  IsPullback.lift_snd _ _ _ _

/-- This parameter-retaining target still satisfies the unchanged original cubic equation. -/
@[reassoc] theorem completeIdentityActionGraphStageParameterizedTarget_contraction :
    completeIdentityActionGraphStageParameterizedTarget K n h m ≫ (r) ≫
        originalStageToCompatibleProj K n h m ≫ completePointToIntegralCubic K n h 0 =
      (p) ≫ completeIdentityFiniteInput K n h 0 m ≫ completeIdentityActionTarget K n h 0 := by
  rw [completeIdentityActionGraphStageParameterizedTarget_projection_assoc,
    completeIdentityActionGraphStageOriginalLift_contraction,
    completeIdentityActionGraphStageOriginalProjection_input_assoc]

end FLT.Mazur.PolygonInfinitesimalStages
